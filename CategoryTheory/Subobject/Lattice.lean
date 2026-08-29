/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The lattice of subobjects

We provide the `SemilatticeInf` with `OrderTop (Subobject X)` instance when `[HasPullback C]`,
and the `SemilatticeSup (Subobject X)` instance when `[HasImages C] [HasBinaryCoproducts C]`.
-/

@[expose] public section


universe w v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory

namespace MonoOver

section Top

instance {X : C} : Top (MonoOver X) where top := mk (𝟙 _)

instance {X : C} : Inhabited (MonoOver X) :=
  ⟨⊤⟩

/--
Definition of `leTop` / `leTop` 的定义

English:
definition leTop
  signature: (f : MonoOver X)
  body: homMk f.arrow (comp_id _)

@[simp]

中文:
定义 leTop
  签名: (f : MonoOver X)
  定义体: homMk f.arrow (comp_id _)

@[simp]

Depends on / 依赖: comp_id, f.arrow
-/
def leTop (f : MonoOver X) : f ⟶ ⊤ :=
  homMk f.arrow (comp_id _)

@[simp]
/--
theorem `top_left` / 定理 `top_left`

English:
theorem top_left
  given: (X : C)
  statement: ((⊤ : MonoOver X) : C) = X
  proof: rfl

@[simp]

中文:
定理 top_left
  条件: (X : C)
  结论: ((⊤ : MonoOver X) : C) = X
  证明: rfl

@[simp]
-/
theorem top_left (X : C) : ((⊤ : MonoOver X) : C) = X :=
  rfl

@[simp]
/--
theorem `top_arrow` / 定理 `top_arrow`

English:
theorem top_arrow
  given: (X : C)
  statement: (⊤ : MonoOver X).arrow = 𝟙 X
  proof: rfl

中文:
定理 top_arrow
  条件: (X : C)
  结论: (⊤ : MonoOver X).arrow = 𝟙 X
  证明: rfl
-/
theorem top_arrow (X : C) : (⊤ : MonoOver X).arrow = 𝟙 X :=
  rfl

/--
Definition of `mapTop` / `mapTop` 的定义

English:
definition mapTop
  signature: (f : X ⟶ Y) [Mono f]
  body: iso_of_both_ways (homMk (𝟙 _) rfl) (homMk (𝟙 _) (by simp [id_comp f]))

中文:
定义 mapTop
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: iso_of_both_ways (homMk (𝟙 _) rfl) (homMk (𝟙 _) (by simp [id_comp f]))

Depends on / 依赖: id_comp, iso_of_both_ways
-/
def mapTop (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ ≅ mk f :=
  iso_of_both_ways (homMk (𝟙 _) rfl) (homMk (𝟙 _) (by simp [id_comp f]))

section

variable [HasPullbacks C]

/--
Definition of `pullbackTop` / `pullbackTop` 的定义

English:
definition pullbackTop
  signature: (f : X ⟶ Y)
  body: iso_of_both_ways (leTop _)
    (homMk (pullback.lift f (𝟙 _) (by simp)) (pullback.lift_snd _ _ _))

中文:
定义 pullbackTop
  签名: (f : X ⟶ Y)
  定义体: iso_of_both_ways (leTop _)
    (homMk (pullback.lift f (𝟙 _) (by simp)) (pullback.lift_snd _ _ _))

Depends on / 依赖: iso_of_both_ways, lift_snd, pullback, pullback.lift, pullback.lift_snd
-/
def pullbackTop (f : X ⟶ Y) : (pullback f).obj ⊤ ≅ ⊤ :=
  iso_of_both_ways (leTop _)
    (homMk (pullback.lift f (𝟙 _) (by simp)) (pullback.lift_snd _ _ _))

/--
Definition of `topLEPullbackSelf` / `topLEPullbackSelf` 的定义

English:
definition topLEPullbackSelf
  signature: {A B : C} (f : A ⟶ B) [Mono f]
  body: homMk _ (pullback.lift_snd _ _ rfl)

中文:
定义 topLEPullbackSelf
  签名: {A B : C} (f : A ⟶ B) [单态射 f]
  定义体: homMk _ (pullback.lift_snd _ _ rfl)

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
def topLEPullbackSelf {A B : C} (f : A ⟶ B) [Mono f] :
    (⊤ : MonoOver A) ⟶ (pullback f).obj (mk f) :=
  homMk _ (pullback.lift_snd _ _ rfl)

/--
Definition of `pullbackSelf` / `pullbackSelf` 的定义

English:
definition pullbackSelf
  signature: {A B : C} (f : A ⟶ B) [Mono f]
  body: iso_of_both_ways (leTop _) (topLEPullbackSelf _)

中文:
定义 pullbackSelf
  签名: {A B : C} (f : A ⟶ B) [单态射 f]
  定义体: iso_of_both_ways (leTop _) (topLEPullbackSelf _)

Depends on / 依赖: iso_of_both_ways, topLEPullbackSelf
-/
def pullbackSelf {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) ≅ ⊤ :=
  iso_of_both_ways (leTop _) (topLEPullbackSelf _)

end

end Top

section Bot

variable [HasInitial C] [InitialMonoClass C]

instance {X : C} : Bot (MonoOver X) where bot := mk (initial.to X)

@[simp]
/--
theorem `bot_left` / 定理 `bot_left`

English:
theorem bot_left
  given: (X : C)
  statement: ((⊥ : MonoOver X) : C) = ⊥_ C
  proof: rfl

@[simp]

中文:
定理 bot_left
  条件: (X : C)
  结论: ((⊥ : MonoOver X) : C) = ⊥_ C
  证明: rfl

@[simp]
-/
theorem bot_left (X : C) : ((⊥ : MonoOver X) : C) = ⊥_ C :=
  rfl

@[simp]
/--
theorem `bot_arrow` / 定理 `bot_arrow`

English:
theorem bot_arrow
  given: {X : C}
  statement: (⊥ : MonoOver X).arrow = initial.to X
  proof: rfl

中文:
定理 bot_arrow
  条件: {X : C}
  结论: (⊥ : MonoOver X).arrow = initial.to X
  证明: rfl
-/
theorem bot_arrow {X : C} : (⊥ : MonoOver X).arrow = initial.to X :=
  rfl

/--
Definition of `botLE` / `botLE` 的定义

English:
definition botLE
  signature: {X : C} (f : MonoOver X)
  body: homMk (initial.to _)

中文:
定义 botLE
  签名: {X : C} (f : MonoOver X)
  定义体: homMk (initial.to _)

Depends on / 依赖: initial, initial.to
-/
def botLE {X : C} (f : MonoOver X) : ⊥ ⟶ f :=
  homMk (initial.to _)

/--
Definition of `mapBot` / `mapBot` 的定义

English:
definition mapBot
  signature: (f : X ⟶ Y) [Mono f]
  body: iso_of_both_ways (homMk (initial.to _)) (homMk (𝟙 _))

中文:
定义 mapBot
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: iso_of_both_ways (homMk (initial.to _)) (homMk (𝟙 _))

Depends on / 依赖: initial, initial.to, iso_of_both_ways
-/
def mapBot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ ≅ ⊥ :=
  iso_of_both_ways (homMk (initial.to _)) (homMk (𝟙 _))

end Bot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/--
Definition of `botCoeIsoZero` / `botCoeIsoZero` 的定义

English:
definition botCoeIsoZero
  signature: {B : C}
  body: initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

中文:
定义 botCoeIsoZero
  签名: {B : C}
  定义体: initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsInitial, initialIsInitial, initialIsInitial.uniqueUpToIso, uniqueUpToIso, zeroIsInitial
-/
def botCoeIsoZero {B : C} : ((⊥ : MonoOver B) : C) ≅ 0 :=
  initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

/--
theorem `bot_arrow_eq_zero` / 定理 `bot_arrow_eq_zero`

English:
theorem bot_arrow_eq_zero
  given: [HasZeroMorphisms C] {B : C}
  statement: (⊥ : MonoOver B).arrow = 0
  proof: zero_of_source_iso_zero _ botCoeIsoZero

中文:
定理 bot_arrow_eq_zero
  条件: [有ZeroMorphisms C] {B : C}
  结论: (⊥ : MonoOver B).arrow = 0
  证明: zero_of_source_iso_zero _ botCoeIsoZero

Depends on / 依赖: botCoeIsoZero, zero_of_source_iso_zero
-/
theorem bot_arrow_eq_zero [HasZeroMorphisms C] {B : C} : (⊥ : MonoOver B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

set_option backward.isDefEq.respectTransparency false in
/-- `simp`-normal form of `bot_arrow_eq_zero`. -/
@[simp]
/--
theorem `initialTo_b_eq_zero` / 定理 `initialTo_b_eq_zero`

English:
theorem initialTo_b_eq_zero
  given: [HasZeroMorphisms C] {B : C}
  statement: initial.to B = 0
  proof: by
  rw [← bot_arrow]; rw [bot_arrow_eq_zero]

中文:
定理 initialTo_b_eq_zero
  条件: [有ZeroMorphisms C] {B : C}
  结论: initial.to B = 0
  证明: by
  rw [← bot_arrow]; rw [bot_arrow_eq_zero]

Depends on / 依赖: bot_arrow, bot_arrow_eq_zero
-/
theorem initialTo_b_eq_zero [HasZeroMorphisms C] {B : C} : initial.to B = 0 := by
  rw [← bot_arrow]; rw [bot_arrow_eq_zero]

end ZeroOrderBot

section Inf

variable [HasPullbacks C]

set_option backward.defeqAttrib.useBackward true in
/-- When `[HasPullbacks C]`, `MonoOver A` has "intersections", functorial in both arguments.

As `MonoOver A` is only a preorder, this doesn't satisfy the axioms of `SemilatticeInf`,
but we reuse all the names from `SemilatticeInf` because they will be used to construct
`SemilatticeInf (Subobject A)` shortly.
-/
@[simps]
/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: {A : C}
  body: pullback f.arrow ⋙ map f.arrow
  map k :=
    { app := fun g => by
        apply homMk _ _
        · apply pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k.hom.left) _
          rw [pullback.condition]; rw [assoc]; rw [w k]
        dsimp
        rw [pullback.lift_snd_assoc]; rw [assoc]; rw [w k] }

中文:
定义 下确界
  签名: {A : C}
  定义体: pullback f.arrow ⋙ map f.arrow
  map k :=
    { app := fun g => by
        apply homMk _ _
        · apply pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k.hom.left) _
          rw [pullback.condition]; rw [assoc]; rw [w k]
        dsimp
        rw [pullback.lift_snd_assoc]; rw [assoc]; rw [w k] }

Depends on / 依赖: f.arrow, pullback
-/
def inf {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A where
  obj f := pullback f.arrow ⋙ map f.arrow
  map k :=
    { app := fun g => by
        apply homMk _ _
        · apply pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ k.hom.left) _
          rw [pullback.condition]; rw [assoc]; rw [w k]
        dsimp
        rw [pullback.lift_snd_assoc]; rw [assoc]; rw [w k] }

/--
Definition of `infLELeft` / `infLELeft` 的定义

English:
definition infLELeft
  signature: {A : C} (f g : MonoOver A)
  body: homMk _ rfl

中文:
定义 infLELeft
  签名: {A : C} (f g : MonoOver A)
  定义体: homMk _ rfl
-/
def infLELeft {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ f :=
  homMk _ rfl

/--
Definition of `infLERight` / `infLERight` 的定义

English:
definition infLERight
  signature: {A : C} (f g : MonoOver A)
  body: homMk _ pullback.condition

中文:
定义 infLERight
  签名: {A : C} (f g : MonoOver A)
  定义体: homMk _ pullback.condition

Depends on / 依赖: condition, pullback, pullback.condition
-/
def infLERight {A : C} (f g : MonoOver A) : (inf.obj f).obj g ⟶ g :=
  homMk _ pullback.condition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `leInf` / `leInf` 的定义

English:
definition leInf
  signature: {A : C} (f g h : MonoOver A)
  body: fun k₁ k₂ => homMk (pullback.lift k₂.hom.left k₁.hom.left (by simp))

中文:
定义 leInf
  签名: {A : C} (f g h : MonoOver A)
  定义体: fun k₁ k₂ => homMk (pullback.lift k₂.hom.left k₁.hom.left (by simp))

Depends on / 依赖: hom.left, pullback, pullback.lift
-/
def leInf {A : C} (f g h : MonoOver A) : (h ⟶ f) -> (h ⟶ g) -> (h ⟶ (inf.obj f).obj g) :=
  fun k₁ k₂ => homMk (pullback.lift k₂.hom.left k₁.hom.left (by simp))

end Inf

section Sup

variable [HasImages C] [HasBinaryCoproducts C]

/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: {A : C}
  body: Functor.curryObj ((forget A).prod (forget A) ⋙ Functor.uncurry.obj Over.coprod ⋙ image)

中文:
定义 上确界
  签名: {A : C}
  定义体: Functor.curryObj ((forget A).prod (forget A) ⋙ Functor.uncurry.obj Over.coprod ⋙ image)

Depends on / 依赖: Functor, Functor.curryObj, Functor.uncurry.obj, Over.coprod, coprod, curryObj, forget, uncurry
-/
def sup {A : C} : MonoOver A ⥤ MonoOver A ⥤ MonoOver A :=
  Functor.curryObj ((forget A).prod (forget A) ⋙ Functor.uncurry.obj Over.coprod ⋙ image)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `leSupLeft` / `leSupLeft` 的定义

English:
definition leSupLeft
  signature: {A : C} (f g : MonoOver A)
  body: by
  refine homMk (coprod.inl ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inl_desc]
  rfl

中文:
定义 leSupLeft
  签名: {A : C} (f g : MonoOver A)
  定义体: by
  refine homMk (coprod.inl ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inl_desc]
  rfl

Depends on / 依赖: Category, Category.assoc, coprod, coprod.inl, coprod.inl_desc, factorThruImage, image.fac, inl_desc
-/
def leSupLeft {A : C} (f g : MonoOver A) : f ⟶ (sup.obj f).obj g := by
  refine homMk (coprod.inl ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inl_desc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `leSupRight` / `leSupRight` 的定义

English:
definition leSupRight
  signature: {A : C} (f g : MonoOver A)
  body: by
  refine homMk (coprod.inr ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inr_desc]
  rfl

中文:
定义 leSupRight
  签名: {A : C} (f g : MonoOver A)
  定义体: by
  refine homMk (coprod.inr ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inr_desc]
  rfl

Depends on / 依赖: Category, Category.assoc, coprod, coprod.inr, coprod.inr_desc, factorThruImage, image.fac, inr_desc
-/
def leSupRight {A : C} (f g : MonoOver A) : g ⟶ (sup.obj f).obj g := by
  refine homMk (coprod.inr ≫ factorThruImage _) ?_
  erw [Category.assoc, image.fac, coprod.inr_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `supLe` / `supLe` 的定义

English:
definition supLe
  signature: {A : C} (f g h : MonoOver A)
  body: by
  intro k₁ k₂
  refine homMk ?_ ?_
  · apply image.lift ⟨_, h.arrow, coprod.desc k₁.hom.left k₂.hom.left, _⟩
    ext
    · simp [w k₁]
    · simp [w k₂]
  · apply image.lift_fac

中文:
定义 supLe
  签名: {A : C} (f g h : MonoOver A)
  定义体: by
  intro k₁ k₂
  refine homMk ?_ ?_
  · apply image.lift ⟨_, h.arrow, coprod.desc k₁.hom.left k₂.hom.left, _⟩
    ext
    · simp [w k₁]
    · simp [w k₂]
  · apply image.lift_fac

Depends on / 依赖: coprod, coprod.desc, h.arrow, hom.left, image.lift, image.lift_fac, lift_fac
-/
def supLe {A : C} (f g h : MonoOver A) : (f ⟶ h) -> (g ⟶ h) -> ((sup.obj f).obj g ⟶ h) := by
  intro k₁ k₂
  refine homMk ?_ ?_
  · apply image.lift ⟨_, h.arrow, coprod.desc k₁.hom.left k₂.hom.left, _⟩
    ext
    · simp [w k₁]
    · simp [w k₂]
  · apply image.lift_fac

end Sup

end MonoOver

namespace Subobject

section OrderTop

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: {X : C}
  body: Quotient.mk'' ⊤
  le_top := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.leTop f⟩

中文:
实例 orderTop
  签名: {X : C}
  定义体: Quotient.mk'' ⊤
  le_top := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.leTop f⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance orderTop {X : C} : OrderTop (Subobject X) where
  top := Quotient.mk'' ⊤
  le_top := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.leTop f⟩

instance {X : C} : Inhabited (Subobject X) :=
  ⟨⊤⟩

/--
theorem `top_eq_id` / 定理 `top_eq_id`

English:
theorem top_eq_id
  given: (B : C)
  statement: (⊤ : Subobject B) = Subobject.mk (𝟙 B)
  proof: rfl

中文:
定理 top_eq_id
  条件: (B : C)
  结论: (⊤ : Subobject B) = Subobject.mk (𝟙 B)
  证明: rfl
-/
theorem top_eq_id (B : C) : (⊤ : Subobject B) = Subobject.mk (𝟙 B) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `underlyingIso_top_hom` / 定理 `underlyingIso_top_hom`

English:
theorem underlyingIso_top_hom
  given: {B : C}
  statement: (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow
  proof: by
  convert! underlyingIso_hom_comp_eq_mk (𝟙 B)
  simp only [comp_id]

中文:
定理 underlyingIso_top_hom
  条件: {B : C}
  结论: (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow
  证明: by
  convert! underlyingIso_hom_comp_eq_mk (𝟙 B)
  simp only [comp_id]

Depends on / 依赖: comp_id, convert, underlyingIso_hom_comp_eq_mk
-/
theorem underlyingIso_top_hom {B : C} : (underlyingIso (𝟙 B)).hom = (⊤ : Subobject B).arrow := by
  convert! underlyingIso_hom_comp_eq_mk (𝟙 B)
  simp only [comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `top_arrow_isIso` / 实例 `top_arrow_isIso`

English:
instance top_arrow_isIso
  signature: {B : C}
  body: by
  rw [← underlyingIso_top_hom]
  infer_instance

@[reassoc (attr := simp)]

中文:
实例 top_arrow_isIso
  签名: {B : C}
  定义体: by
  rw [← underlyingIso_top_hom]
  infer_instance

@[reassoc (attr := simp)]

Depends on / 依赖: infer_instance, underlyingIso_top_hom
-/
instance top_arrow_isIso {B : C} : IsIso (⊤ : Subobject B).arrow := by
  rw [← underlyingIso_top_hom]
  infer_instance

@[reassoc (attr := simp)]
/--
theorem `underlyingIso_inv_top_arrow` / 定理 `underlyingIso_inv_top_arrow`

English:
theorem underlyingIso_inv_top_arrow
  given: {B : C}
  proof: underlyingIso_arrow _

@[simp]

中文:
定理 underlyingIso_inv_top_arrow
  条件: {B : C}
  证明: underlyingIso_arrow _

@[simp]

Depends on / 依赖: underlyingIso_arrow
-/
theorem underlyingIso_inv_top_arrow {B : C} :
    (underlyingIso _).inv ≫ (⊤ : Subobject B).arrow = 𝟙 B :=
  underlyingIso_arrow _

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: (f : X ⟶ Y) [Mono f]
  statement: (map f).obj ⊤ = Subobject.mk f
  proof: Quotient.sound' ⟨MonoOver.mapTop f⟩

中文:
定理 map_top
  条件: (f : X ⟶ Y) [单态射 f]
  结论: (map f).obj ⊤ = Subobject.mk f
  证明: Quotient.sound' ⟨MonoOver.mapTop f⟩

Depends on / 依赖: MonoOver, MonoOver.mapTop, Quotient, Quotient.sound, mapTop
-/
theorem map_top (f : X ⟶ Y) [Mono f] : (map f).obj ⊤ = Subobject.mk f :=
  Quotient.sound' ⟨MonoOver.mapTop f⟩

/--
theorem `top_factors` / 定理 `top_factors`

English:
theorem top_factors
  given: {A B : C} (f : A ⟶ B)
  statement: (⊤ : Subobject B).Factors f
  proof: ⟨f, comp_id _⟩

中文:
定理 top_factors
  条件: {A B : C} (f : A ⟶ B)
  结论: (⊤ : Subobject B).Factors f
  证明: ⟨f, comp_id _⟩

Depends on / 依赖: comp_id
-/
theorem top_factors {A B : C} (f : A ⟶ B) : (⊤ : Subobject B).Factors f :=
  ⟨f, comp_id _⟩

/--
theorem `isIso_iff_mk_eq_top` / 定理 `isIso_iff_mk_eq_top`

English:
theorem isIso_iff_mk_eq_top
  given: {X Y : C} (f : X ⟶ Y) [Mono f]
  statement: IsIso f ↔ mk f = ⊤
  proof: ⟨fun _ => mk_eq_mk_of_comm _ _ (asIso f) (Category.comp_id _), fun h => by
    rw [← ofMkLEMk_comp h.le]; rw [Category.comp_id]
    exact (isoOfMkEqMk _ _ h).isIso_hom⟩

中文:
定理 isIso_iff_mk_eq_top
  条件: {X Y : C} (f : X ⟶ Y) [单态射 f]
  结论: 是同构 f ↔ mk f = ⊤
  证明: ⟨fun _ => mk_eq_mk_of_comm _ _ (asIso f) (Category.comp_id _), fun h => by
    rw [← ofMkLEMk_comp h.le]; rw [Category.comp_id]
    exact (isoOfMkEqMk _ _ h).isIso_hom⟩

Depends on / 依赖: Category, Category.comp_id, comp_id, h.le, isIso_hom, isoOfMkEqMk, mk_eq_mk_of_comm, ofMkLEMk_comp
-/
theorem isIso_iff_mk_eq_top {X Y : C} (f : X ⟶ Y) [Mono f] : IsIso f ↔ mk f = ⊤ :=
  ⟨fun _ => mk_eq_mk_of_comm _ _ (asIso f) (Category.comp_id _), fun h => by
    rw [← ofMkLEMk_comp h.le]; rw [Category.comp_id]
    exact (isoOfMkEqMk _ _ h).isIso_hom⟩

/--
theorem `isIso_arrow_iff_eq_top` / 定理 `isIso_arrow_iff_eq_top`

English:
theorem isIso_arrow_iff_eq_top
  given: {Y : C} (P : Subobject Y)
  statement: IsIso P.arrow ↔ P = ⊤
  proof: by
  rw [isIso_iff_mk_eq_top]; rw [mk_arrow]

中文:
定理 isIso_arrow_iff_eq_top
  条件: {Y : C} (P : Subobject Y)
  结论: 是同构 P.arrow ↔ P = ⊤
  证明: by
  rw [isIso_iff_mk_eq_top]; rw [mk_arrow]

Depends on / 依赖: isIso_iff_mk_eq_top, mk_arrow
-/
theorem isIso_arrow_iff_eq_top {Y : C} (P : Subobject Y) : IsIso P.arrow ↔ P = ⊤ := by
  rw [isIso_iff_mk_eq_top]; rw [mk_arrow]

/--
Instance `isIso_top_arrow` / 实例 `isIso_top_arrow`

English:
instance isIso_top_arrow
  signature: {Y : C}
  body: by rw [isIso_arrow_iff_eq_top]

中文:
实例 isIso_top_arrow
  签名: {Y : C}
  定义体: by rw [isIso_arrow_iff_eq_top]

Depends on / 依赖: isIso_arrow_iff_eq_top
-/
instance isIso_top_arrow {Y : C} : IsIso (⊤ : Subobject Y).arrow := by rw [isIso_arrow_iff_eq_top]

/--
theorem `mk_eq_top_of_isIso` / 定理 `mk_eq_top_of_isIso`

English:
theorem mk_eq_top_of_isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: mk f = ⊤
  proof: (isIso_iff_mk_eq_top f).mp inferInstance

中文:
定理 mk_eq_top_of_isIso
  条件: {X Y : C} (f : X ⟶ Y) [是同构 f]
  结论: mk f = ⊤
  证明: (isIso_iff_mk_eq_top f).mp inferInstance

Depends on / 依赖: isIso_iff_mk_eq_top
-/
theorem mk_eq_top_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : mk f = ⊤ :=
  (isIso_iff_mk_eq_top f).mp inferInstance

/--
theorem `eq_top_of_isIso_arrow` / 定理 `eq_top_of_isIso_arrow`

English:
theorem eq_top_of_isIso_arrow
  given: {Y : C} (P : Subobject Y) [IsIso P.arrow]
  statement: P = ⊤
  proof: (isIso_arrow_iff_eq_top P).mp inferInstance

中文:
定理 eq_top_of_isIso_arrow
  条件: {Y : C} (P : Subobject Y) [是同构 P.arrow]
  结论: P = ⊤
  证明: (isIso_arrow_iff_eq_top P).mp inferInstance

Depends on / 依赖: isIso_arrow_iff_eq_top
-/
theorem eq_top_of_isIso_arrow {Y : C} (P : Subobject Y) [IsIso P.arrow] : P = ⊤ :=
  (isIso_arrow_iff_eq_top P).mp inferInstance

/--
lemma `epi_iff_mk_eq_top` / 引理 `epi_iff_mk_eq_top`

English:
lemma epi_iff_mk_eq_top
  given: [Balanced C] (f : X ⟶ Y) [Mono f]
  proof: by
  rw [← isIso_iff_mk_eq_top]
  exact ⟨fun _ => isIso_of_mono_of_epi f, fun _ => inferInstance⟩

中文:
引理 epi_iff_mk_eq_top
  条件: [Balanced C] (f : X ⟶ Y) [单态射 f]
  证明: by
  rw [← isIso_iff_mk_eq_top]
  exact ⟨fun _ => isIso_of_mono_of_epi f, fun _ => inferInstance⟩

Depends on / 依赖: isIso_iff_mk_eq_top, isIso_of_mono_of_epi
-/
lemma epi_iff_mk_eq_top [Balanced C] (f : X ⟶ Y) [Mono f] :
    Epi f ↔ Subobject.mk f = ⊤ := by
  rw [← isIso_iff_mk_eq_top]
  exact ⟨fun _ => isIso_of_mono_of_epi f, fun _ => inferInstance⟩

section

variable [HasPullbacks C]

/--
theorem `pullback_top` / 定理 `pullback_top`

English:
theorem pullback_top
  given: (f : X ⟶ Y)
  statement: (pullback f).obj ⊤ = ⊤
  proof: Quotient.sound' ⟨MonoOver.pullbackTop f⟩

中文:
定理 pullback_top
  条件: (f : X ⟶ Y)
  结论: (pullback f).obj ⊤ = ⊤
  证明: Quotient.sound' ⟨MonoOver.pullbackTop f⟩

Depends on / 依赖: MonoOver, MonoOver.pullbackTop, Quotient, Quotient.sound, pullbackTop
-/
theorem pullback_top (f : X ⟶ Y) : (pullback f).obj ⊤ = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackTop f⟩

/--
theorem `pullback_self` / 定理 `pullback_self`

English:
theorem pullback_self
  given: {A B : C} (f : A ⟶ B) [Mono f]
  statement: (pullback f).obj (mk f) = ⊤
  proof: Quotient.sound' ⟨MonoOver.pullbackSelf f⟩

中文:
定理 pullback_self
  条件: {A B : C} (f : A ⟶ B) [单态射 f]
  结论: (pullback f).obj (mk f) = ⊤
  证明: Quotient.sound' ⟨MonoOver.pullbackSelf f⟩

Depends on / 依赖: MonoOver, MonoOver.pullbackSelf, Quotient, Quotient.sound, pullbackSelf
-/
theorem pullback_self {A B : C} (f : A ⟶ B) [Mono f] : (pullback f).obj (mk f) = ⊤ :=
  Quotient.sound' ⟨MonoOver.pullbackSelf f⟩

end

end OrderTop

section OrderBot

variable [HasInitial C] [InitialMonoClass C]

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: {X : C}
  body: Quotient.mk'' ⊥
  bot_le := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.botLE f⟩

中文:
实例 orderBot
  签名: {X : C}
  定义体: Quotient.mk'' ⊥
  bot_le := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.botLE f⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance orderBot {X : C} : OrderBot (Subobject X) where
  bot := Quotient.mk'' ⊥
  bot_le := by
    refine Quotient.ind' fun f => ?_
    exact ⟨MonoOver.botLE f⟩

/--
theorem `bot_eq_initial_to` / 定理 `bot_eq_initial_to`

English:
theorem bot_eq_initial_to
  given: {B : C}
  statement: (⊥ : Subobject B) = Subobject.mk (initial.to B)
  proof: rfl

中文:
定理 bot_eq_initial_to
  条件: {B : C}
  结论: (⊥ : Subobject B) = Subobject.mk (initial.to B)
  证明: rfl
-/
theorem bot_eq_initial_to {B : C} : (⊥ : Subobject B) = Subobject.mk (initial.to B) :=
  rfl

/--
Definition of `botCoeIsoInitial` / `botCoeIsoInitial` 的定义

English:
definition botCoeIsoInitial
  signature: {B : C}
  body: underlyingIso _

中文:
定义 botCoeIsoInitial
  签名: {B : C}
  定义体: underlyingIso _

Depends on / 依赖: Preconnected, Preconnected.coe, underlyingIso
-/
def botCoeIsoInitial {B : C} : ((⊥ : Subobject B) : C) ≅ ⊥_ C :=
  underlyingIso _

/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : X ⟶ Y) [Mono f]
  statement: (map f).obj ⊥ = ⊥
  proof: Quotient.sound' ⟨MonoOver.mapBot f⟩

中文:
定理 map_bot
  条件: (f : X ⟶ Y) [单态射 f]
  结论: (map f).obj ⊥ = ⊥
  证明: Quotient.sound' ⟨MonoOver.mapBot f⟩

Depends on / 依赖: MonoOver, MonoOver.mapBot, Quotient, Quotient.sound, h.coe, mapBot
-/
theorem map_bot (f : X ⟶ Y) [Mono f] : (map f).obj ⊥ = ⊥ :=
  Quotient.sound' ⟨MonoOver.mapBot f⟩

end OrderBot

section ZeroOrderBot

variable [HasZeroObject C]

open ZeroObject

/--
Definition of `botCoeIsoZero` / `botCoeIsoZero` 的定义

English:
definition botCoeIsoZero
  signature: {B : C}
  body: botCoeIsoInitial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

中文:
定义 botCoeIsoZero
  签名: {B : C}
  定义体: botCoeIsoInitial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

Depends on / 依赖: Connected, Connected.coe, HasZeroObject, HasZeroObject.zeroIsInitial, botCoeIsoInitial, initialIsInitial, initialIsInitial.uniqueUpToIso, uniqueUpToIso, zeroIsInitial
-/
def botCoeIsoZero {B : C} : ((⊥ : Subobject B) : C) ≅ 0 :=
  botCoeIsoInitial ≪≫ initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial

variable [HasZeroMorphisms C]

/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  given: {B : C}
  statement: (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B)
  proof: mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
    (by simp)

@[simp]

中文:
定理 bot_eq_zero
  条件: {B : C}
  结论: (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B)
  证明: mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
    (by simp)

@[simp]

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsInitial, h.coe, initialIsInitial, initialIsInitial.uniqueUpToIso, mk_eq_mk_of_comm, uniqueUpToIso, zeroIsInitial
-/
theorem bot_eq_zero {B : C} : (⊥ : Subobject B) = Subobject.mk (0 : 0 ⟶ B) :=
  mk_eq_mk_of_comm _ _ (initialIsInitial.uniqueUpToIso HasZeroObject.zeroIsInitial)
    (by simp)

@[simp]
/--
theorem `bot_arrow` / 定理 `bot_arrow`

English:
theorem bot_arrow
  given: {B : C}
  statement: (⊥ : Subobject B).arrow = 0
  proof: zero_of_source_iso_zero _ botCoeIsoZero

中文:
定理 bot_arrow
  条件: {B : C}
  结论: (⊥ : Subobject B).arrow = 0
  证明: zero_of_source_iso_zero _ botCoeIsoZero

Depends on / 依赖: botCoeIsoZero, zero_of_source_iso_zero
-/
theorem bot_arrow {B : C} : (⊥ : Subobject B).arrow = 0 :=
  zero_of_source_iso_zero _ botCoeIsoZero

set_option backward.isDefEq.respectTransparency false in
/--
theorem `bot_factors_iff_zero` / 定理 `bot_factors_iff_zero`

English:
theorem bot_factors_iff_zero
  given: {A B : C} (f : A ⟶ B)
  statement: (⊥ : Subobject B).Factors f ↔ f = 0
  proof: ⟨by
    rintro ⟨h, rfl⟩
    simp only [MonoOver.bot_arrow_eq_zero, MonoOver.bot_left, comp_zero],
   by
    rintro rfl
    exact ⟨0, by simp⟩⟩

中文:
定理 bot_factors_iff_zero
  条件: {A B : C} (f : A ⟶ B)
  结论: (⊥ : Subobject B).Factors f ↔ f = 0
  证明: ⟨by
    rintro ⟨h, rfl⟩
    simp only [MonoOver.bot_arrow_eq_zero, MonoOver.bot_left, comp_zero],
   by
    rintro rfl
    exact ⟨0, by simp⟩⟩

Depends on / 依赖: MonoOver, MonoOver.bot_arrow_eq_zero, MonoOver.bot_left, bot_arrow_eq_zero, bot_left, comp_zero
-/
theorem bot_factors_iff_zero {A B : C} (f : A ⟶ B) : (⊥ : Subobject B).Factors f ↔ f = 0 :=
  ⟨by
    rintro ⟨h, rfl⟩
    simp only [MonoOver.bot_arrow_eq_zero, MonoOver.bot_left, comp_zero],
   by
    rintro rfl
    exact ⟨0, by simp⟩⟩

/--
theorem `mk_eq_bot_iff_zero` / 定理 `mk_eq_bot_iff_zero`

English:
theorem mk_eq_bot_iff_zero
  given: {f : X ⟶ Y} [Mono f]
  statement: Subobject.mk f = ⊥ ↔ f = 0
  proof: ⟨fun h => by simpa [h, bot_factors_iff_zero] using mk_factors_self f, fun h =>
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial) (by simp [h])⟩

中文:
定理 mk_eq_bot_iff_zero
  条件: {f : X ⟶ Y} [单态射 f]
  结论: Subobject.mk f = ⊥ ↔ f = 0
  证明: ⟨fun h => by simpa [h, bot_factors_iff_zero] using mk_factors_self f, fun h =>
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial) (by simp [h])⟩

Depends on / 依赖: HasZeroObject, HasZeroObject.zeroIsoInitial, bot_factors_iff_zero, isoZeroOfMonoEqZero, mk_eq_mk_of_comm, mk_factors_self, zeroIsoInitial
-/
theorem mk_eq_bot_iff_zero {f : X ⟶ Y} [Mono f] : Subobject.mk f = ⊥ ↔ f = 0 :=
  ⟨fun h => by simpa [h, bot_factors_iff_zero] using mk_factors_self f, fun h =>
    mk_eq_mk_of_comm _ _ ((isoZeroOfMonoEqZero h).trans HasZeroObject.zeroIsoInitial) (by simp [h])⟩

end ZeroOrderBot

section Functor

variable (C)

/-- Sending `X : C` to `Subobject X` is a contravariant functor `Cᵒᵖ ⥤ Type`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: [HasPullbacks C]
  body: Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

中文:
定义 functor
  签名: [有Pullbacks C]
  定义体: Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

Depends on / 依赖: Subobject, X.unop
-/
def functor [HasPullbacks C] : Cᵒᵖ ⥤ Type max u₁ v₁ where
  obj X := Subobject X.unop
  map f := ↾(pullback f.unop).obj
  map_id _ := by ext : 3; simp [pullback_id]
  map_comp _ _ := by ext : 3; simp [pullback_comp]

end Functor

section SemilatticeInfTop

variable [HasPullbacks C]

/--
Definition of `inf` / `inf` 的定义

English:
definition inf
  signature: {A : C}
  body: ThinSkeleton.map₂ MonoOver.inf

中文:
定义 下确界
  签名: {A : C}
  定义体: ThinSkeleton.map₂ MonoOver.inf

Depends on / 依赖: MonoOver, MonoOver.inf, ThinSkeleton, ThinSkeleton.map
-/
def inf {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.inf

/--
theorem `inf_le_left` / 定理 `inf_le_left`

English:
theorem inf_le_left
  given: {A : C} (f g : Subobject A)
  statement: (inf.obj f).obj g <= f
  proof: Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLELeft _ _⟩

中文:
定理 inf_le_left
  条件: {A : C} (f g : Subobject A)
  结论: (下确界.obj f).obj g <= f
  证明: Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLELeft _ _⟩

Depends on / 依赖: MonoOver, MonoOver.infLELeft, Quotient, Quotient.inductionOn, exists_adj_of_nontrivial, h.coe.exists_adj_of_nontrivial, infLELeft
-/
theorem inf_le_left {A : C} (f g : Subobject A) : (inf.obj f).obj g <= f :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLELeft _ _⟩

/--
theorem `inf_le_right` / 定理 `inf_le_right`

English:
theorem inf_le_right
  given: {A : C} (f g : Subobject A)
  statement: (inf.obj f).obj g <= g
  proof: Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLERight _ _⟩

中文:
定理 inf_le_right
  条件: {A : C} (f g : Subobject A)
  结论: (下确界.obj f).obj g <= g
  证明: Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLERight _ _⟩

Depends on / 依赖: MonoOver, MonoOver.infLERight, Quotient, Quotient.inductionOn, infLERight
-/
theorem inf_le_right {A : C} (f g : Subobject A) : (inf.obj f).obj g <= g :=
  Quotient.inductionOn₂' f g fun _ _ => ⟨MonoOver.infLERight _ _⟩

/--
theorem `le_inf` / 定理 `le_inf`

English:
theorem le_inf
  given: {A : C} (h f g : Subobject A)
  statement: h <= f -> h <= g -> h <= (inf.obj f).obj g
  proof: Quotient.inductionOn₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨MonoOver.leInf _ _ _ k l⟩)

中文:
定理 le_inf
  条件: {A : C} (h f g : Subobject A)
  结论: h <= f -> h <= g -> h <= (下确界.obj f).obj g
  证明: Quotient.inductionOn₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨MonoOver.leInf _ _ _ k l⟩)

Depends on / 依赖: MonoOver, MonoOver.leInf, Quotient, Quotient.inductionOn
-/
theorem le_inf {A : C} (h f g : Subobject A) : h <= f -> h <= g -> h <= (inf.obj f).obj g :=
  Quotient.inductionOn₃' h f g
    (by
      rintro f g h ⟨k⟩ ⟨l⟩
      exact ⟨MonoOver.leInf _ _ _ k l⟩)

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: {B : C}
  body: fun m n => (inf.obj m).obj n
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

@[reassoc]

中文:
实例 semilatticeInf
  签名: {B : C}
  定义体: fun m n => (inf.obj m).obj n
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

@[reassoc]

Depends on / 依赖: inf.obj
-/
instance semilatticeInf {B : C} : SemilatticeInf (Subobject B) where
  inf := fun m n => (inf.obj m).obj n
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf := le_inf

@[reassoc]
/--
lemma `inf_comp_left` / 引理 `inf_comp_left`

English:
lemma inf_comp_left
  given: {A : C} (f g : Subobject A)
  proof: ofLE_arrow (inf_le_left f g)

@[reassoc]

中文:
引理 inf_comp_left
  条件: {A : C} (f g : Subobject A)
  证明: ofLE_arrow (inf_le_left f g)

@[reassoc]

Depends on / 依赖: inf_le_left, ofLE_arrow
-/
lemma inf_comp_left {A : C} (f g : Subobject A) :
   (ofLE (f ⊓ g) f (by simp)) ≫ f.arrow = (f ⊓ g).arrow :=
  ofLE_arrow (inf_le_left f g)

@[reassoc]
/--
lemma `inf_comp_right` / 引理 `inf_comp_right`

English:
lemma inf_comp_right
  given: {A : C} (f g : Subobject A)
  proof: ofLE_arrow (inf_le_right f g)

中文:
引理 inf_comp_right
  条件: {A : C} (f g : Subobject A)
  证明: ofLE_arrow (inf_le_right f g)

Depends on / 依赖: inf_le_right, ofLE_arrow
-/
lemma inf_comp_right {A : C} (f g : Subobject A) :
   (ofLE (f ⊓ g) g (by simp)) ≫ g.arrow = (f ⊓ g).arrow :=
  ofLE_arrow (inf_le_right f g)

/--
theorem `factors_left_of_inf_factors` / 定理 `factors_left_of_inf_factors`

English:
theorem factors_left_of_inf_factors
  statement: {A B : C} {X Y : Subobject B} {f : A ⟶ B}
  proof: factors_of_le _ (inf_le_left _ _) h

中文:
定理 factors_left_of_inf_factors
  结论: {A B : C} {X Y : Subobject B} {f : A ⟶ B}
  证明: factors_of_le _ (inf_le_left _ _) h

Depends on / 依赖: factors_of_le, inf_le_left
-/
theorem factors_left_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : X.Factors f :=
  factors_of_le _ (inf_le_left _ _) h

/--
theorem `factors_right_of_inf_factors` / 定理 `factors_right_of_inf_factors`

English:
theorem factors_right_of_inf_factors
  statement: {A B : C} {X Y : Subobject B} {f : A ⟶ B}
  proof: factors_of_le _ (inf_le_right _ _) h

@[simp]

中文:
定理 factors_right_of_inf_factors
  结论: {A B : C} {X Y : Subobject B} {f : A ⟶ B}
  证明: factors_of_le _ (inf_le_right _ _) h

@[simp]

Depends on / 依赖: factors_of_le, inf_le_right
-/
theorem factors_right_of_inf_factors {A B : C} {X Y : Subobject B} {f : A ⟶ B}
    (h : (X ⊓ Y).Factors f) : Y.Factors f :=
  factors_of_le _ (inf_le_right _ _) h

@[simp]
/--
theorem `inf_factors` / 定理 `inf_factors`

English:
theorem inf_factors
  given: {A B : C} {X Y : Subobject B} (f : A ⟶ B)
  proof: ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    apply Quotient.ind₂'
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩

中文:
定理 inf_factors
  条件: {A B : C} {X Y : Subobject B} (f : A ⟶ B)
  证明: ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    apply Quotient.ind₂'
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩

Depends on / 依赖: Quotient, Quotient.ind, factors_left_of_inf_factors, factors_right_of_inf_factors, lift_snd_assoc, pullback, pullback.lift_snd_assoc, revert
-/
theorem inf_factors {A B : C} {X Y : Subobject B} (f : A ⟶ B) :
    (X ⊓ Y).Factors f ↔ X.Factors f ∧ Y.Factors f :=
  ⟨fun h => ⟨factors_left_of_inf_factors h, factors_right_of_inf_factors h⟩, by
    revert X Y
    apply Quotient.ind₂'
    rintro X Y ⟨⟨g₁, rfl⟩, ⟨g₂, hg₂⟩⟩
    exact ⟨_, pullback.lift_snd_assoc _ _ hg₂ _⟩⟩

/--
theorem `inf_isPullback` / 定理 `inf_isPullback`

English:
theorem inf_isPullback
  given: {A : C} (f g : Subobject A)
  proof: by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (f ⊓ g).factorThru (s.fst ≫ f.arrow) ?_)
    ?_ (fun s => ?_) fun _ _ h _ => ?_⟩⟩
  · simpa using ⟨factors_comp_arrow s.fst, by simpa [s.condition] using factors_comp_arrow s.snd⟩
  · cat_disch
  · ext
    simp [s.condition]
  · ext
    simp [← h]

中文:
定理 inf_isPullback
  条件: {A : C} (f g : Subobject A)
  证明: by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (f ⊓ g).factorThru (s.fst ≫ f.arrow) ?_)
    ?_ (fun s => ?_) fun _ _ h _ => ?_⟩⟩
  · simpa using ⟨factors_comp_arrow s.fst, by simpa [s.condition] using factors_comp_arrow s.snd⟩
  · cat_disch
  · ext
    simp [s.condition]
  · ext
    simp [← h]

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.mk, cat_disch, condition, f.arrow, factorThru, factors_comp_arrow, s.condition, s.fst, s.snd
-/
theorem inf_isPullback {A : C} (f g : Subobject A) :
    IsPullback (ofLE (f ⊓ g) f (by simp)) (ofLE (f ⊓ g) g (by simp)) f.arrow g.arrow := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (f ⊓ g).factorThru (s.fst ≫ f.arrow) ?_)
    ?_ (fun s => ?_) fun _ _ h _ => ?_⟩⟩
  · simpa using ⟨factors_comp_arrow s.fst, by simpa [s.condition] using factors_comp_arrow s.snd⟩
  · cat_disch
  · ext
    simp [s.condition]
  · ext
    simp [← h]

/--
theorem `inf_arrow_factors_left` / 定理 `inf_arrow_factors_left`

English:
theorem inf_arrow_factors_left
  given: {B : C} (X Y : Subobject B)
  statement: X.Factors (X ⊓ Y).arrow
  proof: (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) X (inf_le_left X Y), by simp⟩

中文:
定理 inf_arrow_factors_left
  条件: {B : C} (X Y : Subobject B)
  结论: X.Factors (X ⊓ Y).arrow
  证明: (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) X (inf_le_left X Y), by simp⟩

Depends on / 依赖: factors_iff, inf_le_left
-/
theorem inf_arrow_factors_left {B : C} (X Y : Subobject B) : X.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) X (inf_le_left X Y), by simp⟩

/--
theorem `inf_arrow_factors_right` / 定理 `inf_arrow_factors_right`

English:
theorem inf_arrow_factors_right
  given: {B : C} (X Y : Subobject B)
  statement: Y.Factors (X ⊓ Y).arrow
  proof: (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) Y (inf_le_right X Y), by simp⟩

@[simp]

中文:
定理 inf_arrow_factors_right
  条件: {B : C} (X Y : Subobject B)
  结论: Y.Factors (X ⊓ Y).arrow
  证明: (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) Y (inf_le_right X Y), by simp⟩

@[simp]

Depends on / 依赖: factors_iff, inf_le_right
-/
theorem inf_arrow_factors_right {B : C} (X Y : Subobject B) : Y.Factors (X ⊓ Y).arrow :=
  (factors_iff _ _).mpr ⟨ofLE (X ⊓ Y) Y (inf_le_right X Y), by simp⟩

@[simp]
/--
theorem `finset_inf_factors` / 定理 `finset_inf_factors`

English:
theorem finset_inf_factors
  given: {I : Type*} {A B : C} {s : Finset I} {P : I -> Subobject B} (f : A ⟶ B)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [top_factors]
  | insert _ _ _ ih => simp [ih]

中文:
定理 finset_inf_factors
  条件: {I : 类型} {A B : C} {s : 有限集 I} {P : I -> Subobject B} (f : A ⟶ B)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp [top_factors]
  | insert _ _ _ ih => simp [ih]

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on, insert, top_factors
-/
theorem finset_inf_factors {I : Type*} {A B : C} {s : Finset I} {P : I -> Subobject B} (f : A ⟶ B) :
    (s.inf P).Factors f ↔ forall i in s, (P i).Factors f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [top_factors]
  | insert _ _ _ ih => simp [ih]

-- `i` is explicit here because often we'd like to defer a proof of `m`
/--
theorem `finset_inf_arrow_factors` / 定理 `finset_inf_arrow_factors`

English:
theorem finset_inf_arrow_factors
  statement: {I : Type*} {B : C} (s : Finset I) (P : I -> Subobject B) (i : I)
  proof: by
  classical
  revert i m
  induction s using Finset.induction_on with
  | empty => rintro _ ⟨⟩
  | insert _ _ _ ih =>
    intro _ m
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m

中文:
定理 finset_inf_arrow_factors
  结论: {I : 类型} {B : C} (s : 有限集 I) (P : I -> Subobject B) (i : I)
  证明: by
  classical
  revert i m
  induction s using Finset.induction_on with
  | empty => rintro _ ⟨⟩
  | insert _ _ _ ih =>
    intro _ m
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m

Depends on / 依赖: Finset, Finset.induction_on, Finset.inf_insert, Finset.mem_insert, classical, factorThru_arrow, factors_comp_arrow, factors_of_factors_right, induction_on, inf_arrow_factors_left, inf_arrow_factors_right, inf_insert, insert, mem_insert, revert
-/
theorem finset_inf_arrow_factors {I : Type*} {B : C} (s : Finset I) (P : I -> Subobject B) (i : I)
    (m : i in s) : (P i).Factors (s.inf P).arrow := by
  classical
  revert i m
  induction s using Finset.induction_on with
  | empty => rintro _ ⟨⟩
  | insert _ _ _ ih =>
    intro _ m
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_left _ _)]
      exact factors_comp_arrow _
    · rw [← factorThru_arrow _ _ (inf_arrow_factors_right _ _)]
      apply factors_of_factors_right
      exact ih _ m

/--
theorem `inf_eq_map_pullback'` / 定理 `inf_eq_map_pullback'`

English:
theorem inf_eq_map_pullback'
  given: {A : C} (f₁ : MonoOver A) (f₂ : Subobject A)
  proof: by
  induction f₂ using Quotient.inductionOn'
  rfl

中文:
定理 inf_eq_map_pullback'
  条件: {A : C} (f₁ : MonoOver A) (f₂ : Subobject A)
  证明: by
  induction f₂ using Quotient.inductionOn'
  rfl

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem inf_eq_map_pullback' {A : C} (f₁ : MonoOver A) (f₂ : Subobject A) :
    (Subobject.inf.obj (Quotient.mk'' f₁)).obj f₂ =
      (Subobject.map f₁.arrow).obj ((Subobject.pullback f₁.arrow).obj f₂) := by
  induction f₂ using Quotient.inductionOn'
  rfl

/--
theorem `inf_eq_map_pullback` / 定理 `inf_eq_map_pullback`

English:
theorem inf_eq_map_pullback
  given: {A : C} (f₁ : Subobject A) (f₂ : Subobject A)
  proof: by
  convert! inf_eq_map_pullback' (representative.obj f₁) f₂
  ext1
  nth_rw 1 [← thinSkeleton_mk_representative_eq_self f₁]
  congr

中文:
定理 inf_eq_map_pullback
  条件: {A : C} (f₁ : Subobject A) (f₂ : Subobject A)
  证明: by
  convert! inf_eq_map_pullback' (representative.obj f₁) f₂
  ext1
  nth_rw 1 [← thinSkeleton_mk_representative_eq_self f₁]
  congr

Depends on / 依赖: convert, inf_eq_map_pullback, nth_rw, representative, representative.obj, thinSkeleton_mk_representative_eq_self
-/
theorem inf_eq_map_pullback {A : C} (f₁ : Subobject A) (f₂ : Subobject A) :
    (f₁ ⊓ f₂ : Subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) := by
  convert! inf_eq_map_pullback' (representative.obj f₁) f₂
  ext1
  nth_rw 1 [← thinSkeleton_mk_representative_eq_self f₁]
  congr

/--
theorem `prod_eq_inf` / 定理 `prod_eq_inf`

English:
theorem prod_eq_inf
  given: {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂]
  proof: by
  apply le_antisymm
  · refine le_inf _ _ _ (Limits.prod.fst.le) (Limits.prod.snd.le)
  · apply leOfHom
    exact prod.lift (inf_le_left _ _).hom (inf_le_right _ _).hom

中文:
定理 prod_eq_inf
  条件: {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂]
  证明: by
  apply le_antisymm
  · refine le_inf _ _ _ (Limits.prod.fst.le) (Limits.prod.snd.le)
  · apply leOfHom
    exact prod.lift (inf_le_left _ _).hom (inf_le_right _ _).hom

Depends on / 依赖: Limits, Limits.prod.fst.le, Limits.prod.snd.le, inf_le_left, inf_le_right, leOfHom, le_antisymm, le_inf, prod.lift
-/
theorem prod_eq_inf {A : C} {f₁ f₂ : Subobject A} [HasBinaryProduct f₁ f₂] :
    (f₁ ⨯ f₂) = f₁ ⊓ f₂ := by
  apply le_antisymm
  · refine le_inf _ _ _ (Limits.prod.fst.le) (Limits.prod.snd.le)
  · apply leOfHom
    exact prod.lift (inf_le_left _ _).hom (inf_le_right _ _).hom

/--
theorem `inf_def` / 定理 `inf_def`

English:
theorem inf_def
  given: {B : C} (m m' : Subobject B)
  statement: m ⊓ m' = (inf.obj m).obj m'
  proof: rfl

中文:
定理 inf_def
  条件: {B : C} (m m' : Subobject B)
  结论: m ⊓ m' = (下确界.obj m).obj m'
  证明: rfl
-/
theorem inf_def {B : C} (m m' : Subobject B) : m ⊓ m' = (inf.obj m).obj m' :=
  rfl

/--
theorem `inf_pullback` / 定理 `inf_pullback`

English:
theorem inf_pullback
  given: {X Y : C} (g : X ⟶ Y) (f₁ f₂)
  proof: by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullbackIsPullback f₁.arrow g), ← pullback_comp,
    pullback.condition]
  rfl

中文:
定理 inf_pullback
  条件: {X Y : C} (g : X ⟶ Y) (f₁ f₂)
  证明: by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullbackIsPullback f₁.arrow g), ← pullback_comp,
    pullback.condition]
  rfl

Depends on / 依赖: Quotient, Quotient.ind, condition, inf_def, inf_eq_map_pullback, map_pullback, pullback, pullback.condition, pullbackIsPullback, pullback_comp, revert
-/
theorem inf_pullback {X Y : C} (g : X ⟶ Y) (f₁ f₂) :
    (pullback g).obj (f₁ ⊓ f₂) = (pullback g).obj f₁ ⊓ (pullback g).obj f₂ := by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← pullback_comp, ←
    map_pullback pullback.condition (pullbackIsPullback f₁.arrow g), ← pullback_comp,
    pullback.condition]
  rfl

/--
theorem `inf_map` / 定理 `inf_map`

English:
theorem inf_map
  given: {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂)
  proof: by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  dsimp
  rw [pullback_comp]; rw [pullback_map_self]

中文:
定理 inf_map
  条件: {X Y : C} (g : Y ⟶ X) [单态射 g] (f₁ f₂)
  证明: by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  dsimp
  rw [pullback_comp]; rw [pullback_map_self]

Depends on / 依赖: Quotient, Quotient.ind, inf_def, inf_eq_map_pullback, map_comp, pullback_comp, pullback_map_self, revert
-/
theorem inf_map {X Y : C} (g : Y ⟶ X) [Mono g] (f₁ f₂) :
    (map g).obj (f₁ ⊓ f₂) = (map g).obj f₁ ⊓ (map g).obj f₂ := by
  revert f₁
  apply Quotient.ind'
  intro f₁
  erw [inf_def, inf_def, inf_eq_map_pullback', inf_eq_map_pullback', ← map_comp]
  dsimp
  rw [pullback_comp]; rw [pullback_map_self]

end SemilatticeInfTop

section SemilatticeSup

variable [HasImages C] [HasBinaryCoproducts C]

/--
Definition of `sup` / `sup` 的定义

English:
definition sup
  signature: {A : C}
  body: ThinSkeleton.map₂ MonoOver.sup

中文:
定义 上确界
  签名: {A : C}
  定义体: ThinSkeleton.map₂ MonoOver.sup

Depends on / 依赖: MonoOver, MonoOver.sup, ThinSkeleton, ThinSkeleton.map
-/
def sup {A : C} : Subobject A ⥤ Subobject A ⥤ Subobject A :=
  ThinSkeleton.map₂ MonoOver.sup

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: {B : C}
  body: fun m n => (sup.obj m).obj n
  le_sup_left := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupLeft _ _⟩
  le_sup_right := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupRight _ _⟩
  sup_le := fun m n k =>
    Quotient.inductionOn₃' m n k fun _ _ _ ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩

中文:
实例 semilatticeSup
  签名: {B : C}
  定义体: fun m n => (sup.obj m).obj n
  le_sup_left := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupLeft _ _⟩
  le_sup_right := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupRight _ _⟩
  sup_le := fun m n k =>
    Quotient.inductionOn₃' m n k fun _ _ _ ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩

Depends on / 依赖: sup.obj
-/
instance semilatticeSup {B : C} : SemilatticeSup (Subobject B) where
  sup := fun m n => (sup.obj m).obj n
  le_sup_left := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupLeft _ _⟩
  le_sup_right := fun m n => Quotient.inductionOn₂' m n fun _ _ => ⟨MonoOver.leSupRight _ _⟩
  sup_le := fun m n k =>
    Quotient.inductionOn₃' m n k fun _ _ _ ⟨i⟩ ⟨j⟩ => ⟨MonoOver.supLe _ _ _ i j⟩

/--
theorem `sup_factors_of_factors_left` / 定理 `sup_factors_of_factors_left`

English:
theorem sup_factors_of_factors_left
  given: {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f)
  proof: factors_of_le f le_sup_left P

中文:
定理 sup_factors_of_factors_left
  条件: {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f)
  证明: factors_of_le f le_sup_left P

Depends on / 依赖: factors_of_le, le_sup_left
-/
theorem sup_factors_of_factors_left {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : X.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_left P

/--
theorem `sup_factors_of_factors_right` / 定理 `sup_factors_of_factors_right`

English:
theorem sup_factors_of_factors_right
  given: {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f)
  proof: factors_of_le f le_sup_right P

中文:
定理 sup_factors_of_factors_right
  条件: {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f)
  证明: factors_of_le f le_sup_right P

Depends on / 依赖: factors_of_le, le_sup_right
-/
theorem sup_factors_of_factors_right {A B : C} {X Y : Subobject B} {f : A ⟶ B} (P : Y.Factors f) :
    (X ⊔ Y).Factors f :=
  factors_of_le f le_sup_right P

variable [HasInitial C] [InitialMonoClass C]

/--
theorem `finset_sup_factors` / 定理 `finset_sup_factors`

English:
theorem finset_sup_factors
  statement: {I : Type*} {A B : C} {s : Finset I} {P : I -> Subobject B} {f : A ⟶ B}
  proof: by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => rintro ⟨_, ⟨⟨⟩, _⟩⟩
  | insert _ _ _ ih =>
    rintro ⟨j, ⟨m, h⟩⟩
    simp only [Finset.sup_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)

中文:
定理 finset_sup_factors
  结论: {I : 类型} {A B : C} {s : 有限集 I} {P : I -> Subobject B} {f : A ⟶ B}
  证明: by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => rintro ⟨_, ⟨⟨⟩, _⟩⟩
  | insert _ _ _ ih =>
    rintro ⟨j, ⟨m, h⟩⟩
    simp only [Finset.sup_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert, Finset.sup_insert, classical, induction_on, insert, mem_insert, revert, sup_factors_of_factors_left, sup_factors_of_factors_right, sup_insert
-/
theorem finset_sup_factors {I : Type*} {A B : C} {s : Finset I} {P : I -> Subobject B} {f : A ⟶ B}
    (h : exists i in s, (P i).Factors f) : (s.sup P).Factors f := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => rintro ⟨_, ⟨⟨⟩, _⟩⟩
  | insert _ _ _ ih =>
    rintro ⟨j, ⟨m, h⟩⟩
    simp only [Finset.sup_insert]
    simp only [Finset.mem_insert] at m
    rcases m with (rfl | m)
    · exact sup_factors_of_factors_left h
    · exact sup_factors_of_factors_right (ih ⟨j, ⟨m, h⟩⟩)

end SemilatticeSup

section Lattice

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: [HasInitial C] [InitialMonoClass C] {B : C}
  body: { Subobject.orderTop, Subobject.orderBot with }

中文:
实例 boundedOrder
  签名: [HasInitial C] [InitialMono类 C] {B : C}
  定义体: { Subobject.orderTop, Subobject.orderBot with }

Depends on / 依赖: Subobject, Subobject.orderBot, Subobject.orderTop, orderBot, orderTop
-/
instance boundedOrder [HasInitial C] [InitialMonoClass C] {B : C} : BoundedOrder (Subobject B) :=
  { Subobject.orderTop, Subobject.orderBot with }

variable [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]

instance {B : C} : Lattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup with }

end Lattice

section Inf

variable [LocallySmall.{w} C] [WellPowered.{w} C]

/--
Definition of `wideCospan` / `wideCospan` 的定义

English:
definition wideCospan
  signature: {A : C} (s : Set (Subobject A))
  body: WidePullbackShape.wideCospan A
    (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow

@[simp]

中文:
定义 wideCospan
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: WidePullbackShape.wideCospan A
    (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow

@[simp]

Depends on / 依赖: Subobject, WidePullbackShape, WidePullbackShape.wideCospan, equivShrink, wideCospan
-/
def wideCospan {A : C} (s : Set (Subobject A)) : WidePullbackShape (equivShrink _ '' s) ⥤ C :=
  WidePullbackShape.wideCospan A
    (fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j : C)) fun j =>
    ((equivShrink (Subobject A)).symm j).arrow

@[simp]
/--
theorem `wideCospan_map_term` / 定理 `wideCospan_map_term`

English:
theorem wideCospan_map_term
  given: {A : C} (s : Set (Subobject A)) (j)
  proof: rfl

中文:
定理 wideCospan_map_term
  条件: {A : C} (s : 集合 (Subobject A)) (j)
  证明: rfl
-/
theorem wideCospan_map_term {A : C} (s : Set (Subobject A)) (j) :
    (wideCospan s).map (WidePullbackShape.Hom.term j) =
      ((equivShrink (Subobject A)).symm j).arrow :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `leInfCone` / `leInfCone` 的定义

English:
definition leInfCone
  signature: {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, f <= g)
  body: WidePullbackShape.mkCone f.arrow
    (fun j =>
      underlying.map
        (homOfLE
          (k _
            (by
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              simpa using m))))
    (by simp)

@[simp]

中文:
定义 leInfCone
  签名: {A : C} (s : 集合 (Subobject A)) (f : Subobject A) (k : 对任意 g in s, f <= g)
  定义体: WidePullbackShape.mkCone f.arrow
    (fun j =>
      underlying.map
        (homOfLE
          (k _
            (by
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              simpa using m))))
    (by simp)

@[simp]

Depends on / 依赖: WidePullbackShape, WidePullbackShape.mkCone, f.arrow, homOfLE, mkCone, underlying, underlying.map
-/
def leInfCone {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, f <= g) :
    Cone (wideCospan s) :=
  WidePullbackShape.mkCone f.arrow
    (fun j =>
      underlying.map
        (homOfLE
          (k _
            (by
              rcases j with ⟨-, ⟨g, ⟨m, rfl⟩⟩⟩
              simpa using m))))
    (by simp)

@[simp]
/--
theorem `leInfCone_π_app_none` / 定理 `leInfCone_π_app_none`

English:
theorem leInfCone_π_app_none
  statement: {A : C} (s : Set (Subobject A)) (f : Subobject A)
  proof: rfl

中文:
定理 leInfCone_π_app_none
  结论: {A : C} (s : 集合 (Subobject A)) (f : Subobject A)
  证明: rfl
-/
theorem leInfCone_π_app_none {A : C} (s : Set (Subobject A)) (f : Subobject A)
    (k : forall g in s, f <= g) : (leInfCone s f k).π.app none = f.arrow :=
  rfl

variable [HasWidePullbacks.{w} C]

/--
Definition of `widePullback` / `widePullback` 的定义

English:
definition widePullback
  signature: {A : C} (s : Set (Subobject A))
  body: Limits.limit (wideCospan s)

中文:
定义 widePullback
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: Limits.limit (wideCospan s)

Depends on / 依赖: Limits, Limits.limit, wideCospan
-/
def widePullback {A : C} (s : Set (Subobject A)) : C :=
  Limits.limit (wideCospan s)

/--
Definition of `widePullbackι` / `widePullbackι` 的定义

English:
definition widePullbackι
  signature: {A : C} (s : Set (Subobject A))
  body: Limits.limit.π (wideCospan s) none

中文:
定义 widePullbackι
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: Limits.limit.π (wideCospan s) none

Depends on / 依赖: Limits, Limits.limit, wideCospan
-/
def widePullbackι {A : C} (s : Set (Subobject A)) : widePullback s ⟶ A :=
  Limits.limit.π (wideCospan s) none

set_option backward.isDefEq.respectTransparency false in
/--
Instance `widePullbackι_mono` / 实例 `widePullbackι_mono`

English:
instance widePullbackι_mono
  signature: {A : C} (s : Set (Subobject A))
  body: ⟨fun u v h =>
    limit.hom_ext fun j => by
      cases j
      · exact h
      · apply (cancel_mono ((equivShrink (Subobject A)).symm _).arrow).1
        rw [assoc]; rw [assoc]
        erw [limit.w (wideCospan s) (WidePullbackShape.Hom.term _)]
        exact h⟩

中文:
实例 widePullbackι_mono
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: ⟨fun u v h =>
    limit.hom_ext fun j => by
      cases j
      · exact h
      · apply (cancel_mono ((equivShrink (Subobject A)).symm _).arrow).1
        rw [assoc]; rw [assoc]
        erw [limit.w (wideCospan s) (WidePullbackShape.Hom.term _)]
        exact h⟩

Depends on / 依赖: Subobject, WidePullbackShape, WidePullbackShape.Hom.term, cancel_mono, equivShrink, hom_ext, limit.hom_ext, limit.w, wideCospan
-/
instance widePullbackι_mono {A : C} (s : Set (Subobject A)) : Mono (widePullbackι s) :=
  ⟨fun u v h =>
    limit.hom_ext fun j => by
      cases j
      · exact h
      · apply (cancel_mono ((equivShrink (Subobject A)).symm _).arrow).1
        rw [assoc]; rw [assoc]
        erw [limit.w (wideCospan s) (WidePullbackShape.Hom.term _)]
        exact h⟩

/--
Definition of `sInf` / `sInf` 的定义

English:
definition sInf
  signature: {A : C} (s : Set (Subobject A))
  body: Subobject.mk (widePullbackι s)

中文:
定义 sInf
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: Subobject.mk (widePullbackι s)

Depends on / 依赖: Subobject, Subobject.mk
-/
def sInf {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (widePullbackι s)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sInf_le` / 定理 `sInf_le`

English:
theorem sInf_le
  given: {A : C} (s : Set (Subobject A)) (f) (hf : f in s)
  statement: sInf s <= f
  proof: by
  fapply le_of_comm
  · exact (underlyingIso _).hom ≫
      Limits.limit.π (wideCospan s)
        (some ⟨equivShrink (Subobject A) f,
          Set.mem_image_of_mem (equivShrink (Subobject A)) hf⟩) ≫
      eqToHom (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _))
  · dsimp [sInf]
    simp only [Category.assoc, ← underlyingIso_hom_comp_eq_mk,
      Iso.cancel_iso_hom_left]
    convert! limit.w (wideCospan s) (WidePullbackShape.Hom.term _)
    simp

中文:
定理 sInf_le
  条件: {A : C} (s : 集合 (Subobject A)) (f) (hf : f in s)
  结论: sInf s <= f
  证明: by
  fapply le_of_comm
  · exact (underlyingIso _).hom ≫
      Limits.limit.π (wideCospan s)
        (some ⟨equivShrink (Subobject A) f,
          Set.mem_image_of_mem (equivShrink (Subobject A)) hf⟩) ≫
      eqToHom (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _))
  · dsimp [sInf]
    simp only [Category.assoc, ← underlyingIso_hom_comp_eq_mk,
      Iso.cancel_iso_hom_left]
    convert! limit.w (wideCospan s) (WidePullbackShape.Hom.term _)
    simp

Depends on / 依赖: Category, Category.assoc, Equiv.symm_apply_apply, Iso.cancel_iso_hom_left, Limits, Limits.limit, Set.mem_image_of_mem, Subobject, WidePullbackShape, WidePullbackShape.Hom.term, cancel_iso_hom_left, congr_arg, convert, eqToHom, equivShrink, fapply, le_of_comm, limit.w, mem_image_of_mem, symm_apply_apply
-/
theorem sInf_le {A : C} (s : Set (Subobject A)) (f) (hf : f in s) : sInf s <= f := by
  fapply le_of_comm
  · exact (underlyingIso _).hom ≫
      Limits.limit.π (wideCospan s)
        (some ⟨equivShrink (Subobject A) f,
          Set.mem_image_of_mem (equivShrink (Subobject A)) hf⟩) ≫
      eqToHom (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _))
  · dsimp [sInf]
    simp only [Category.assoc, ← underlyingIso_hom_comp_eq_mk,
      Iso.cancel_iso_hom_left]
    convert! limit.w (wideCospan s) (WidePullbackShape.Hom.term _)
    simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_sInf` / 定理 `le_sInf`

English:
theorem le_sInf
  given: {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, f <= g)
  proof: by
  fapply le_of_comm
  · exact Limits.limit.lift _ (leInfCone s f k) ≫ (underlyingIso _).inv
  · dsimp [sInf]
    rw [assoc]; rw [underlyingIso_arrow]; rw [widePullbackι]; rw [limit.lift_π]; rw [leInfCone_π_app_none]

中文:
定理 le_sInf
  条件: {A : C} (s : 集合 (Subobject A)) (f : Subobject A) (k : 对任意 g in s, f <= g)
  证明: by
  fapply le_of_comm
  · exact Limits.limit.lift _ (leInfCone s f k) ≫ (underlyingIso _).inv
  · dsimp [sInf]
    rw [assoc]; rw [underlyingIso_arrow]; rw [widePullbackι]; rw [limit.lift_π]; rw [leInfCone_π_app_none]

Depends on / 依赖: Limits, Limits.limit.lift, fapply, leInfCone, le_of_comm, limit.lift_, underlyingIso, underlyingIso_arrow
-/
theorem le_sInf {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, f <= g) :
    f <= sInf s := by
  fapply le_of_comm
  · exact Limits.limit.lift _ (leInfCone s f k) ≫ (underlyingIso _).inv
  · dsimp [sInf]
    rw [assoc]; rw [underlyingIso_arrow]; rw [widePullbackι]; rw [limit.lift_π]; rw [leInfCone_π_app_none]

/--
Instance `completeSemilatticeInf` / 实例 `completeSemilatticeInf`

English:
instance completeSemilatticeInf
  signature: {B : C}
  body: sInf
  isGLB_sInf _ := ⟨sInf_le _, le_sInf _⟩

中文:
实例 completeSemilatticeInf
  签名: {B : C}
  定义体: sInf
  isGLB_sInf _ := ⟨sInf_le _, le_sInf _⟩
-/
instance completeSemilatticeInf {B : C} : CompleteSemilatticeInf (Subobject B) where
  sInf := sInf
  isGLB_sInf _ := ⟨sInf_le _, le_sInf _⟩

end Inf

section Sup

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]

/--
Definition of `smallCoproductDesc` / `smallCoproductDesc` 的定义

English:
definition smallCoproductDesc
  signature: {A : C} (s : Set (Subobject A))
  body: Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow

中文:
定义 smallCoproductDesc
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow

Depends on / 依赖: Limits, Limits.Sigma.desc, Subobject, equivShrink
-/
def smallCoproductDesc {A : C} (s : Set (Subobject A)) :=
  Limits.Sigma.desc fun j : equivShrink _ '' s => ((equivShrink (Subobject A)).symm j).arrow

variable [HasImages C]

/--
Definition of `sSup` / `sSup` 的定义

English:
definition sSup
  signature: {A : C} (s : Set (Subobject A))
  body: Subobject.mk (image.ι (smallCoproductDesc s))

中文:
定义 sSup
  签名: {A : C} (s : 集合 (Subobject A))
  定义体: Subobject.mk (image.ι (smallCoproductDesc s))

Depends on / 依赖: Subobject, Subobject.mk, smallCoproductDesc
-/
def sSup {A : C} (s : Set (Subobject A)) : Subobject A :=
  Subobject.mk (image.ι (smallCoproductDesc s))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_sSup` / 定理 `le_sSup`

English:
theorem le_sSup
  given: {A : C} (s : Set (Subobject A)) (f) (hf : f in s)
  statement: f <= sSup s
  proof: by
  fapply le_of_comm
  · refine eqToHom ?_ ≫ Sigma.ι _ ⟨equivShrink (Subobject A) f, by simpa [Set.mem_image] using hf⟩
      ≫ factorThruImage _ ≫ (underlyingIso _).inv
    exact (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
  · simp [sSup, smallCoproductDesc]

中文:
定理 le_sSup
  条件: {A : C} (s : 集合 (Subobject A)) (f) (hf : f in s)
  结论: f <= sSup s
  证明: by
  fapply le_of_comm
  · refine eqToHom ?_ ≫ Sigma.ι _ ⟨equivShrink (Subobject A) f, by simpa [Set.mem_image] using hf⟩
      ≫ factorThruImage _ ≫ (underlyingIso _).inv
    exact (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
  · simp [sSup, smallCoproductDesc]

Depends on / 依赖: Equiv.symm_apply_apply, Set.mem_image, Subobject, congr_arg, eqToHom, equivShrink, factorThruImage, fapply, le_of_comm, mem_image, smallCoproductDesc, symm_apply_apply, underlyingIso
-/
theorem le_sSup {A : C} (s : Set (Subobject A)) (f) (hf : f in s) : f <= sSup s := by
  fapply le_of_comm
  · refine eqToHom ?_ ≫ Sigma.ι _ ⟨equivShrink (Subobject A) f, by simpa [Set.mem_image] using hf⟩
      ≫ factorThruImage _ ≫ (underlyingIso _).inv
    exact (congr_arg (fun X : Subobject A => (X : C)) (Equiv.symm_apply_apply _ _).symm)
  · simp [sSup, smallCoproductDesc]

/--
theorem `symm_apply_mem_iff_mem_image` / 定理 `symm_apply_mem_iff_mem_image`

English:
theorem symm_apply_mem_iff_mem_image
  given: {α β : Type*} (e : α ≃ β) (s : Set α) (x : β)
  proof: ⟨fun h => ⟨e.symm x, h, by simp⟩, by
    rintro ⟨a, m, rfl⟩
    simpa using m⟩

中文:
定理 symm_apply_mem_iff_mem_image
  条件: {α β : 类型} (e : α ≃ β) (s : 集合 α) (x : β)
  证明: ⟨fun h => ⟨e.symm x, h, by simp⟩, by
    rintro ⟨a, m, rfl⟩
    simpa using m⟩

Depends on / 依赖: e.symm
-/
theorem symm_apply_mem_iff_mem_image {α β : Type*} (e : α ≃ β) (s : Set α) (x : β) :
    e.symm x in s ↔ x in e '' s :=
  ⟨fun h => ⟨e.symm x, h, by simp⟩, by
    rintro ⟨a, m, rfl⟩
    simpa using m⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sSup_le` / 定理 `sSup_le`

English:
theorem sSup_le
  given: {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, g <= f)
  proof: by
  fapply le_of_comm
  · refine (underlyingIso _).hom ≫ image.lift ⟨_, f.arrow, ?_, ?_⟩
    · refine Sigma.desc ?_
      rintro ⟨g, m⟩
      refine underlying.map (homOfLE (k _ ?_))
      simpa using m
    · ext
      dsimp [smallCoproductDesc]
      simp
  · dsimp [sSup]
    rw [assoc]; rw [image.lift_fac]; rw [underlyingIso_hom_comp_eq_mk]

中文:
定理 sSup_le
  条件: {A : C} (s : 集合 (Subobject A)) (f : Subobject A) (k : 对任意 g in s, g <= f)
  证明: by
  fapply le_of_comm
  · refine (underlyingIso _).hom ≫ image.lift ⟨_, f.arrow, ?_, ?_⟩
    · refine Sigma.desc ?_
      rintro ⟨g, m⟩
      refine underlying.map (homOfLE (k _ ?_))
      simpa using m
    · ext
      dsimp [smallCoproductDesc]
      simp
  · dsimp [sSup]
    rw [assoc]; rw [image.lift_fac]; rw [underlyingIso_hom_comp_eq_mk]

Depends on / 依赖: Sigma.desc, f.arrow, fapply, homOfLE, image.lift, image.lift_fac, le_of_comm, lift_fac, smallCoproductDesc, underlying, underlying.map, underlyingIso, underlyingIso_hom_comp_eq_mk
-/
theorem sSup_le {A : C} (s : Set (Subobject A)) (f : Subobject A) (k : forall g in s, g <= f) :
    sSup s <= f := by
  fapply le_of_comm
  · refine (underlyingIso _).hom ≫ image.lift ⟨_, f.arrow, ?_, ?_⟩
    · refine Sigma.desc ?_
      rintro ⟨g, m⟩
      refine underlying.map (homOfLE (k _ ?_))
      simpa using m
    · ext
      dsimp [smallCoproductDesc]
      simp
  · dsimp [sSup]
    rw [assoc]; rw [image.lift_fac]; rw [underlyingIso_hom_comp_eq_mk]

/--
Instance `completeSemilatticeSup` / 实例 `completeSemilatticeSup`

English:
instance completeSemilatticeSup
  signature: {B : C}
  body: sSup
  isLUB_sSup _ := ⟨le_sSup _, sSup_le _⟩

中文:
实例 completeSemilatticeSup
  签名: {B : C}
  定义体: sSup
  isLUB_sSup _ := ⟨le_sSup _, sSup_le _⟩
-/
instance completeSemilatticeSup {B : C} : CompleteSemilatticeSup (Subobject B) where
  sSup := sSup
  isLUB_sSup _ := ⟨le_sSup _, sSup_le _⟩

end Sup

section CompleteLattice

variable [LocallySmall.{w} C] [WellPowered.{w} C] [HasWidePullbacks.{w} C]
  [HasImages C] [HasCoproducts.{w} C] [InitialMonoClass C]

attribute [local instance] has_smallest_coproducts_of_hasCoproducts

instance {B : C} : CompleteLattice (Subobject B) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup, Subobject.boundedOrder,
    Subobject.completeSemilatticeInf, Subobject.completeSemilatticeSup with }

end CompleteLattice

/--
lemma `subsingleton_of_isInitial` / 引理 `subsingleton_of_isInitial`

English:
lemma subsingleton_of_isInitial
  given: {X : C} (hX : IsInitial X)
  statement: Subsingleton (Subobject X)
  proof: by
  suffices forall (S : Subobject X), S = .mk (𝟙 _) from ⟨by simp [this]⟩
  intro S
  obtain ⟨A, i, _, rfl⟩ := S.mk_surjective
  have fac : hX.to A ≫ i = 𝟙 X := hX.hom_ext _ _
  let e : A ≅ X :=
    { hom := i
      inv := hX.to A
      hom_inv_id := by rw [← cancel_mono i, assoc, fac, id_comp, comp_id]
      inv_hom_id := fac }
  exact mk_eq_mk_of_comm i (𝟙 X) e (by simp [e])

中文:
引理 subsingleton_of_isInitial
  条件: {X : C} (hX : IsInitial X)
  结论: 子单例 (Subobject X)
  证明: by
  suffices forall (S : Subobject X), S = .mk (𝟙 _) from ⟨by simp [this]⟩
  intro S
  obtain ⟨A, i, _, rfl⟩ := S.mk_surjective
  have fac : hX.to A ≫ i = 𝟙 X := hX.hom_ext _ _
  let e : A ≅ X :=
    { hom := i
      inv := hX.to A
      hom_inv_id := by rw [← cancel_mono i, assoc, fac, id_comp, comp_id]
      inv_hom_id := fac }
  exact mk_eq_mk_of_comm i (𝟙 X) e (by simp [e])

Depends on / 依赖: S.mk_surjective, Subobject, cancel_mono, comp_id, hX.hom_ext, hX.to, hom_ext, hom_inv_id, id_comp, inv_hom_id, mk_eq_mk_of_comm, mk_surjective
-/
lemma subsingleton_of_isInitial {X : C} (hX : IsInitial X) : Subsingleton (Subobject X) := by
  suffices forall (S : Subobject X), S = .mk (𝟙 _) from ⟨by simp [this]⟩
  intro S
  obtain ⟨A, i, _, rfl⟩ := S.mk_surjective
  have fac : hX.to A ≫ i = 𝟙 X := hX.hom_ext _ _
  let e : A ≅ X :=
    { hom := i
      inv := hX.to A
      hom_inv_id := by rw [← cancel_mono i, assoc, fac, id_comp, comp_id]
      inv_hom_id := fac }
  exact mk_eq_mk_of_comm i (𝟙 X) e (by simp [e])

/--
lemma `subsingleton_of_isZero` / 引理 `subsingleton_of_isZero`

English:
lemma subsingleton_of_isZero
  given: {X : C} (hX : IsZero X)
  statement: Subsingleton (Subobject X)
  proof: subsingleton_of_isInitial hX.isInitial

中文:
引理 subsingleton_of_isZero
  条件: {X : C} (hX : 是零 X)
  结论: 子单例 (Subobject X)
  证明: subsingleton_of_isInitial hX.isInitial

Depends on / 依赖: hX.isInitial, isInitial, subsingleton_of_isInitial
-/
lemma subsingleton_of_isZero {X : C} (hX : IsZero X) : Subsingleton (Subobject X) :=
  subsingleton_of_isInitial hX.isInitial

section ZeroObject

variable [HasZeroMorphisms C] [HasZeroObject C]

open ZeroObject

/--
theorem `nontrivial_of_not_isZero` / 定理 `nontrivial_of_not_isZero`

English:
theorem nontrivial_of_not_isZero
  given: {X : C} (h : ¬IsZero X)
  statement: Nontrivial (Subobject X)
  proof: ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (isZero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩

中文:
定理 nontrivial_of_not_isZero
  条件: {X : C} (h : ¬是零 X)
  结论: 非平凡 (Subobject X)
  证明: ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (isZero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩

Depends on / 依赖: IsZero, IsZero.of_iso, isZero_zero, isoOfMkEqMk, of_iso
-/
theorem nontrivial_of_not_isZero {X : C} (h : ¬IsZero X) : Nontrivial (Subobject X) :=
  ⟨⟨mk (0 : 0 ⟶ X), mk (𝟙 X), fun w => h (IsZero.of_iso (isZero_zero C) (isoOfMkEqMk _ _ w).symm)⟩⟩

end ZeroObject

section SubobjectSubobject

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `subobjectOrderIso` / `subobjectOrderIso` 的定义

English:
definition subobjectOrderIso
  signature: {X : C} (Y : Subobject X)
  body: ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr (le_of_comm ((underlyingIso _).hom ≫ Z.arrow) (by simp))⟩
  invFun Z := Subobject.mk (ofLE _ _ Z.2)
  left_inv Z := mk_eq_of_comm _ (underlyingIso _) (by cat_disch)
  right_inv Z := Subtype.ext (mk_eq_of_comm _ (underlyingIso _) (by simp [← Iso.eq_inv_comp]))
  map_rel_iff' {W Z} := by
    dsimp
    constructor
    · intro h
      exact le_of_comm (((underlyingIso _).inv ≫ ofLE _ _ (Subtype.mk_le_mk.mp h) ≫
        (underlyingIso _).hom)) (by cat_disch)
    · intro h
      exact Subtype.mk_le_mk.mpr (le_of_comm
        ((underlyingIso _).hom ≫ ofLE _ _ h ≫ (underlyingIso _).inv) (by simp))

中文:
定义 subobjectOrderIso
  签名: {X : C} (Y : Subobject X)
  定义体: ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr (le_of_comm ((underlyingIso _).hom ≫ Z.arrow) (by simp))⟩
  invFun Z := Subobject.mk (ofLE _ _ Z.2)
  left_inv Z := mk_eq_of_comm _ (underlyingIso _) (by cat_disch)
  right_inv Z := Subtype.ext (mk_eq_of_comm _ (underlyingIso _) (by simp [← Iso.eq_inv_comp]))
  map_rel_iff' {W Z} := by
    dsimp
    constructor
    · intro h
      exact le_of_comm (((underlyingIso _).inv ≫ ofLE _ _ (Subtype.mk_le_mk.mp h) ≫
        (underlyingIso _).hom)) (by cat_disch)
    · intro h
      exact Subtype.mk_le_mk.mpr (le_of_comm
        ((underlyingIso _).hom ≫ ofLE _ _ h ≫ (underlyingIso _).inv) (by simp))

Depends on / 依赖: Iso.eq_inv_comp, Set.mem_Iic.mpr, Subobject, Subobject.mk, Subtype, Subtype.ext, Subtype.m, Subtype.mk_le_mk.mp, Y.arrow, Z.arrow, cat_disch, eq_inv_comp, invFun, le_of_comm, left_inv, map_rel_iff, mem_Iic, mk_eq_of_comm, mk_le_mk, right_inv
-/
def subobjectOrderIso {X : C} (Y : Subobject X) : Subobject (Y : C) ≃o Set.Iic Y where
  toFun Z :=
    ⟨Subobject.mk (Z.arrow ≫ Y.arrow),
      Set.mem_Iic.mpr (le_of_comm ((underlyingIso _).hom ≫ Z.arrow) (by simp))⟩
  invFun Z := Subobject.mk (ofLE _ _ Z.2)
  left_inv Z := mk_eq_of_comm _ (underlyingIso _) (by cat_disch)
  right_inv Z := Subtype.ext (mk_eq_of_comm _ (underlyingIso _) (by simp [← Iso.eq_inv_comp]))
  map_rel_iff' {W Z} := by
    dsimp
    constructor
    · intro h
      exact le_of_comm (((underlyingIso _).inv ≫ ofLE _ _ (Subtype.mk_le_mk.mp h) ≫
        (underlyingIso _).hom)) (by cat_disch)
    · intro h
      exact Subtype.mk_le_mk.mpr (le_of_comm
        ((underlyingIso _).hom ≫ ofLE _ _ h ≫ (underlyingIso _).inv) (by simp))

end SubobjectSubobject

end Subobject

end CategoryTheory
