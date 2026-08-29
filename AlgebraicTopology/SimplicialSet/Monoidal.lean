/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# The monoidal category structure on simplicial sets

This file defines an instance of chosen finite products
for the category `SSet`. It follows from the fact
the `SSet` if a category of functors to the category
of types and that the category of types have chosen
finite products. As a result, we obtain a monoidal
category structure on `SSet`.

-/

@[expose] public section

universe u

open Simplicial CategoryTheory MonoidalCategory CartesianMonoidalCategory
  Limits SimplicialObject.Truncated

namespace SSet

@[simp]
/--
lemma `leftUnitor_hom_app_apply` / 引理 `leftUnitor_hom_app_apply`

English:
lemma leftUnitor_hom_app_apply
  given: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ otimes K).obj Δ)
  proof: rfl

@[simp]

中文:
引理 leftUnitor_hom_app_apply
  条件: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ otimes K).obj Δ)
  证明: rfl

@[simp]
-/
lemma leftUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (𝟙_ _ otimes K).obj Δ) :
    dsimp% (fun_ K).hom.app Δ x = x.2 := rfl

@[simp]
/--
lemma `leftUnitor_inv_app_apply` / 引理 `leftUnitor_inv_app_apply`

English:
lemma leftUnitor_inv_app_apply
  given: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ)
  proof: rfl

@[simp]

中文:
引理 leftUnitor_inv_app_apply
  条件: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ)
  证明: rfl

@[simp]
-/
lemma leftUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    dsimp% (fun_ K).inv.app Δ x = ⟨PUnit.unit, x⟩ := rfl

@[simp]
/--
lemma `rightUnitor_hom_app_apply` / 引理 `rightUnitor_hom_app_apply`

English:
lemma rightUnitor_hom_app_apply
  given: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K otimes 𝟙_ _).obj Δ)
  proof: rfl

@[simp]

中文:
引理 rightUnitor_hom_app_apply
  条件: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K otimes 𝟙_ _).obj Δ)
  证明: rfl

@[simp]
-/
lemma rightUnitor_hom_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : (K otimes 𝟙_ _).obj Δ) :
    dsimp% (ρ_ K).hom.app Δ x = x.1 := rfl

@[simp]
/--
lemma `rightUnitor_inv_app_apply` / 引理 `rightUnitor_inv_app_apply`

English:
lemma rightUnitor_inv_app_apply
  given: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ)
  proof: rfl

@[simp]

中文:
引理 rightUnitor_inv_app_apply
  条件: (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ)
  证明: rfl

@[simp]
-/
lemma rightUnitor_inv_app_apply (K : SSet.{u}) {Δ : SimplexCategoryᵒᵖ} (x : K.obj Δ) :
    dsimp% (ρ_ K).inv.app Δ x = ⟨x, PUnit.unit⟩ := rfl

@[simp]
/--
lemma `tensorHom_app_apply` / 引理 `tensorHom_app_apply`

English:
lemma tensorHom_app_apply
  statement: {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
  proof: rfl

@[simp]

中文:
引理 tensorHom_app_apply
  结论: {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
  证明: rfl

@[simp]
-/
lemma tensorHom_app_apply {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K otimes L).obj Δ) :
    dsimp% (f otimesₘ g).app Δ x = ⟨f.app Δ x.1, g.app Δ x.2⟩ := rfl

@[simp]
/--
lemma `whiskerLeft_app_apply` / 引理 `whiskerLeft_app_apply`

English:
lemma whiskerLeft_app_apply
  statement: (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L')
  proof: rfl

@[simp]

中文:
引理 whiskerLeft_app_apply
  结论: (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L')
  证明: rfl

@[simp]
-/
lemma whiskerLeft_app_apply (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L')
    {Δ : SimplexCategoryᵒᵖ} (x : (K otimes L).obj Δ) :
    dsimp% (K ◁ g).app Δ x = ⟨x.1, g.app Δ x.2⟩ := rfl

@[simp]
/--
lemma `whiskerRight_app_apply` / 引理 `whiskerRight_app_apply`

English:
lemma whiskerRight_app_apply
  statement: {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u})
  proof: rfl

@[simp]

中文:
引理 whiskerRight_app_apply
  结论: {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u})
  证明: rfl

@[simp]
-/
lemma whiskerRight_app_apply {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u})
    {Δ : SimplexCategoryᵒᵖ} (x : (K otimes L).obj Δ) :
    dsimp% (f ▷ L).app Δ x = ⟨f.app Δ x.1, x.2⟩ := rfl

@[simp]
/--
lemma `associator_hom_app_apply` / 引理 `associator_hom_app_apply`

English:
lemma associator_hom_app_apply
  statement: (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
  proof: rfl

@[simp]

中文:
引理 associator_hom_app_apply
  结论: (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
  证明: rfl

@[simp]
-/
lemma associator_hom_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : ((K otimes L) otimes M).obj Δ) :
    dsimp% (α_ K L M).hom.app Δ x = ⟨x.1.1, x.1.2, x.2⟩ := rfl

@[simp]
/--
lemma `associator_inv_app_apply` / 引理 `associator_inv_app_apply`

English:
lemma associator_inv_app_apply
  statement: (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
  proof: rfl

中文:
引理 associator_inv_app_apply
  结论: (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
  证明: rfl
-/
lemma associator_inv_app_apply (K L M : SSet.{u}) {Δ : SimplexCategoryᵒᵖ}
    (x : (K otimes L otimes M).obj Δ) :
    dsimp% (α_ K L M).inv.app Δ x = ⟨⟨x.1, x.2.1⟩, x.2.2⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unitHomEquiv` / `unitHomEquiv` 的定义

English:
definition unitHomEquiv
  signature: (K : SSet.{u})
  body: φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ => ↾fun _ => K.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← Functor.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp [-Monoidal.tensorUnit_obj]


中文:
定义 unitHomEquiv
  签名: (K : SSet.{u})
  定义体: φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ => ↾fun _ => K.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← Functor.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp [-Monoidal.tensorUnit_obj]


Depends on / 依赖: PUnit.unit
-/
def unitHomEquiv (K : SSet.{u}) : (𝟙_ _ ⟶ K) ≃ K _⦋0⦌ where
  toFun φ := φ.app _ PUnit.unit
  invFun x :=
    { app := fun Δ => ↾fun _ => K.map (SimplexCategory.const Δ.unop ⦋0⦌ 0).op x
      naturality := fun Δ Δ' f => by
        ext ⟨⟩
        dsimp
        rw [← Functor.map_comp_apply]
        rfl }
  left_inv φ := by
    ext Δ ⟨⟩
    dsimp [-Monoidal.tensorUnit_obj]
    rw [← NatTrans.naturality_apply]
    rfl
  right_inv x := by simp

/--
Definition of `stdSimplex.isTerminalObj₀` / `stdSimplex.isTerminalObj₀` 的定义

English:
definition stdSimplex.isTerminalObj₀
  signature: : IsTerminal (Δ[0] : SSet.{u})
  body: IsTerminal.ofUniqueHom (fun _ => SSet.const (obj₀Equiv.symm 0))
    (fun _ _ => by
      ext ⟨n⟩
      exact objEquiv.injective (by ext; simp))

@[ext]

中文:
定义 stdSimplex.isTerminalObj₀
  签名: : 是终止 (Δ[0] : SSet.{u})
  定义体: IsTerminal.ofUniqueHom (fun _ => SSet.const (obj₀Equiv.symm 0))
    (fun _ _ => by
      ext ⟨n⟩
      exact objEquiv.injective (by ext; simp))

@[ext]

Depends on / 依赖: Equiv.symm, IsTerminal, IsTerminal.ofUniqueHom, SSet.const, injective, objEquiv, objEquiv.injective, ofUniqueHom
-/
def stdSimplex.isTerminalObj₀ : IsTerminal (Δ[0] : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun _ => SSet.const (obj₀Equiv.symm 0))
    (fun _ _ => by
      ext ⟨n⟩
      exact objEquiv.injective (by ext; simp))

@[ext]
/--
lemma `stdSimplex.ext₀` / 引理 `stdSimplex.ext₀`

English:
lemma stdSimplex.ext₀
  given: {X : SSet.{u}} {f g : X ⟶ Δ[0]}
  statement: f = g
  proof: isTerminalObj₀.hom_ext _ _

中文:
引理 stdSimplex.ext₀
  条件: {X : SSet.{u}} {f g : X ⟶ Δ[0]}
  结论: f = g
  证明: isTerminalObj₀.hom_ext _ _

Depends on / 依赖: hom_ext
-/
lemma stdSimplex.ext₀ {X : SSet.{u}} {f g : X ⟶ Δ[0]} : f = g :=
  isTerminalObj₀.hom_ext _ _

instance (X Y : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    [Finite (X.obj n)] [Finite (Y.obj n)] :
    Finite ((X otimes Y).obj n) :=
  inferInstanceAs (Finite (X.obj n × Y.obj n))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟙_ SSet.{u}).Finite
  body: finite_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit)

中文:
实例 :
  签名: (𝟙_ SSet.{u}).有限
  定义体: finite_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit)

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.isTerminalTensorUnit, finite_of_iso, isTerminalTensorUnit, stdSimplex, stdSimplex.isTerminalObj, uniqueUpToIso
-/
instance : (𝟙_ SSet.{u}).Finite :=
  finite_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDimensionLE (𝟙_ SSet.{u}) 0
  body: (hasDimensionLT_iff_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit) _).1 inferInstance

中文:
实例 :
  签名: HasDimensionLE (𝟙_ SSet.{u}) 0
  定义体: (hasDimensionLT_iff_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit) _).1 inferInstance

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.isTerminalTensorUnit, hasDimensionLT_iff_of_iso, isTerminalTensorUnit, stdSimplex, stdSimplex.isTerminalObj, uniqueUpToIso
-/
instance : HasDimensionLE (𝟙_ SSet.{u}) 0 :=
  (hasDimensionLT_iff_of_iso (stdSimplex.isTerminalObj₀.{u}.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit) _).1 inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: opFunctor.{u}.Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

中文:
实例 :
  签名: opFunctor.{u}.幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : opFunctor.{u}.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

namespace Subcomplex

/-- The external product of subcomplexes of simplicial sets. -/
@[simps]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
  body: (A.obj Δ).prod (B.obj Δ)
  map i _ hx := ⟨A.map i hx.1, B.map i hx.2⟩

中文:
定义 乘积
  签名: {X Y : SSet.{u}} (A : X.子复形) (B : Y.子复形)
  定义体: (A.obj Δ).prod (B.obj Δ)
  map i _ hx := ⟨A.map i hx.1, B.map i hx.2⟩

Depends on / 依赖: A.obj, B.obj
-/
def prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) : (X otimes Y).Subcomplex where
  obj Δ := (A.obj Δ).prod (B.obj Δ)
  map i _ hx := ⟨A.map i hx.1, B.map i hx.2⟩

/--
lemma `prod_monotone` / 引理 `prod_monotone`

English:
lemma prod_monotone
  statement: {X Y : SSet.{u}}
  proof: fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩

中文:
引理 prod_monotone
  结论: {X Y : SSet.{u}}
  证明: fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩
-/
lemma prod_monotone {X Y : SSet.{u}}
    {A₁ A₂ : X.Subcomplex} (hX : A₁ <= A₂) {B₁ B₂ : Y.Subcomplex} (hY : B₁ <= B₂) :
    A₁.prod B₁ <= A₂.prod B₂ :=
  fun _ _ hx => ⟨hX _ hx.1, hY _ hx.2⟩

/--
lemma `prod_le_top_prod` / 引理 `prod_le_top_prod`

English:
lemma prod_le_top_prod
  given: {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
  proof: prod_monotone le_top (by rfl)

中文:
引理 prod_le_top_prod
  条件: {X Y : SSet.{u}} (A : X.子复形) (B : Y.子复形)
  证明: prod_monotone le_top (by rfl)

Depends on / 依赖: le_top, prod_monotone
-/
lemma prod_le_top_prod {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    A.prod B <= (⊤ : X.Subcomplex).prod B :=
  prod_monotone le_top (by rfl)

/--
lemma `prod_le_prod_top` / 引理 `prod_le_prod_top`

English:
lemma prod_le_prod_top
  given: {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
  proof: prod_monotone (by rfl) le_top

中文:
引理 prod_le_prod_top
  条件: {X Y : SSet.{u}} (A : X.子复形) (B : Y.子复形)
  证明: prod_monotone (by rfl) le_top

Depends on / 依赖: le_top, prod_monotone
-/
lemma prod_le_prod_top {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    A.prod B <= A.prod ⊤ :=
  prod_monotone (by rfl) le_top

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_tensorHom` / 引理 `range_tensorHom`

English:
lemma range_tensorHom
  given: {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  proof: by
  ext m ⟨y₁, y₂⟩
  constructor
  · rintro ⟨⟨x₁, x₂⟩, h⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    exact ⟨⟨x₁, h.1⟩, ⟨x₂, h.2⟩⟩
  · rintro ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩
    exact ⟨⟨x₁, x₂⟩, rfl⟩

中文:
引理 range_tensorHom
  条件: {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
  证明: by
  ext m ⟨y₁, y₂⟩
  constructor
  · rintro ⟨⟨x₁, x₂⟩, h⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    exact ⟨⟨x₁, h.1⟩, ⟨x₂, h.2⟩⟩
  · rintro ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩
    exact ⟨⟨x₁, x₂⟩, rfl⟩

Depends on / 依赖: Prod.eq_iff_fst_eq_snd_eq, eq_iff_fst_eq_snd_eq
-/
lemma range_tensorHom {X₁ X₂ Y₁ Y₂ : SSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    range (f₁ otimesₘ f₂) = (range f₁).prod (range f₂) := by
  ext m ⟨y₁, y₂⟩
  constructor
  · rintro ⟨⟨x₁, x₂⟩, h⟩
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    exact ⟨⟨x₁, h.1⟩, ⟨x₂, h.2⟩⟩
  · rintro ⟨⟨x₁, rfl⟩, ⟨x₂, rfl⟩⟩
    exact ⟨⟨x₁, x₂⟩, rfl⟩

/-- The isomorphism `(A.prod B).toSSet ≅ A.toSSet ⊗ B.toSSet`. -/
@[simps]
/--
Definition of `prodIso` / `prodIso` 的定义

English:
definition prodIso
  signature: {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex)
  body: CartesianMonoidalCategory.lift
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
  inv := lift (A.ι otimesₘ B.ι) (by
 

中文:
定义 prodIso
  签名: {X Y : SSet.{u}} (A : X.子复形) (B : Y.子复形)
  定义体: CartesianMonoidalCategory.lift
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
  inv := lift (A.ι otimesₘ B.ι) (by
 

Depends on / 依赖: CartesianMonoidalCategory, CartesianMonoidalCategory.lift
-/
def prodIso {X Y : SSet.{u}} (A : X.Subcomplex) (B : Y.Subcomplex) :
    (A.prod B).toSSet ≅ A otimes B where
  hom := CartesianMonoidalCategory.lift
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.fst _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
    (lift ((A.prod B).ι ≫ CartesianMonoidalCategory.snd _ _) (by
      intro _ _ ⟨⟨_, ⟨_, _⟩⟩, _⟩
      cat_disch))
  inv := lift (A.ι otimesₘ B.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact ⟨Subtype.coe_prop _, Subtype.coe_prop _⟩)

end Subcomplex

/--
Definition of `ι₀` / `ι₀` 的定义

English:
definition ι₀
  signature: {X : SSet.{u}}
  body: lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]

中文:
定义 ι₀
  签名: {X : SSet.{u}}
  定义体: lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]

Depends on / 依赖: stdSimplex, stdSimplex.obj
-/
noncomputable def ι₀ {X : SSet.{u}} : X ⟶ X otimes Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]
/--
lemma `ι₀_comp` / 引理 `ι₀_comp`

English:
lemma ι₀_comp
  given: {X Y : SSet.{u}} (f : X ⟶ Y)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₀_comp
  条件: {X Y : SSet.{u}} (f : X ⟶ Y)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₀_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₀_fst` / 引理 `ι₀_fst`

English:
lemma ι₀_fst
  given: (X : SSet.{u})
  statement: ι₀ ≫ fst X _ = 𝟙 X
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₀_fst
  条件: (X : SSet.{u})
  结论: ι₀ ≫ fst X _ = 𝟙 X
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₀_fst (X : SSet.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₀_snd` / 引理 `ι₀_snd`

English:
lemma ι₀_snd
  given: (X : SSet.{u})
  statement: ι₀ ≫ snd X _ = const (stdSimplex.obj₀Equiv.{u}.symm 0)
  proof: rfl

@[simp]

中文:
引理 ι₀_snd
  条件: (X : SSet.{u})
  结论: ι₀ ≫ snd X _ = const (stdSimplex.obj₀Equiv.{u}.symm 0)
  证明: rfl

@[simp]
-/
lemma ι₀_snd (X : SSet.{u}) : ι₀ ≫ snd X _ = const (stdSimplex.obj₀Equiv.{u}.symm 0) := rfl

@[simp]
/--
lemma `ι₀_app_fst` / 引理 `ι₀_app_fst`

English:
lemma ι₀_app_fst
  given: {X : SSet.{u}} {m} (x : X.obj m)
  statement: dsimp% (ι₀.app _ x).1 = x
  proof: rfl

@[simp]

中文:
引理 ι₀_app_fst
  条件: {X : SSet.{u}} {m} (x : X.obj m)
  结论: dsimp% (ι₀.app _ x).1 = x
  证明: rfl

@[simp]
-/
lemma ι₀_app_fst {X : SSet.{u}} {m} (x : X.obj m) : dsimp% (ι₀.app _ x).1 = x := rfl

@[simp]
/--
lemma `ι₀_app_snd_apply` / 引理 `ι₀_app_snd_apply`

English:
lemma ι₀_app_snd_apply
  given: {X : SSet.{u}} {m : Nat} (x : X _⦋m⦌) (k : Fin (m + 1))
  proof: rfl

中文:
引理 ι₀_app_snd_apply
  条件: {X : SSet.{u}} {m : 自然数} (x : X _⦋m⦌) (k : 有限集 (m + 1))
  证明: rfl
-/
lemma ι₀_app_snd_apply {X : SSet.{u}} {m : Nat} (x : X _⦋m⦌) (k : Fin (m + 1)) :
    dsimp% (ι₀.app _ x).2 k = 0 := rfl

/--
Definition of `ι₁` / `ι₁` 的定义

English:
definition ι₁
  signature: {X : SSet.{u}}
  body: lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc (attr := simp)]

中文:
定义 ι₁
  签名: {X : SSet.{u}}
  定义体: lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc (attr := simp)]

Depends on / 依赖: stdSimplex, stdSimplex.obj
-/
noncomputable def ι₁ {X : SSet.{u}} : X ⟶ X otimes Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc (attr := simp)]
/--
lemma `ι₁_fst` / 引理 `ι₁_fst`

English:
lemma ι₁_fst
  given: (X : SSet.{u})
  statement: ι₁ ≫ fst X _ = 𝟙 X
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₁_fst
  条件: (X : SSet.{u})
  结论: ι₁ ≫ fst X _ = 𝟙 X
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₁_fst (X : SSet.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₁_snd` / 引理 `ι₁_snd`

English:
lemma ι₁_snd
  given: (X : SSet.{u})
  statement: ι₁ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 1))
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₁_snd
  条件: (X : SSet.{u})
  结论: ι₁ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 1))
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₁_snd (X : SSet.{u}) : ι₁ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 1)) := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₁_comp` / 引理 `ι₁_comp`

English:
lemma ι₁_comp
  given: {X Y : SSet.{u}} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ι₁_comp
  条件: {X Y : SSet.{u}} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ι₁_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[simp]
/--
lemma `ι₁_app_fst` / 引理 `ι₁_app_fst`

English:
lemma ι₁_app_fst
  given: {X : SSet.{u}} {m} (x : X.obj m)
  statement: dsimp% (ι₁.app _ x).1 = x
  proof: rfl

@[simp]

中文:
引理 ι₁_app_fst
  条件: {X : SSet.{u}} {m} (x : X.obj m)
  结论: dsimp% (ι₁.app _ x).1 = x
  证明: rfl

@[simp]
-/
lemma ι₁_app_fst {X : SSet.{u}} {m} (x : X.obj m) : dsimp% (ι₁.app _ x).1 = x := rfl

@[simp]
/--
lemma `ι₁_app_snd_apply` / 引理 `ι₁_app_snd_apply`

English:
lemma ι₁_app_snd_apply
  given: {X : SSet.{u}} {m : Nat} (x : X _⦋m⦌) (k : Fin (m + 1))
  proof: rfl

中文:
引理 ι₁_app_snd_apply
  条件: {X : SSet.{u}} {m : 自然数} (x : X _⦋m⦌) (k : 有限集 (m + 1))
  证明: rfl
-/
lemma ι₁_app_snd_apply {X : SSet.{u}} {m : Nat} (x : X _⦋m⦌) (k : Fin (m + 1)) :
    dsimp% (ι₁.app _ x).2 k = 1 := rfl

section

variable (X Y : SSet.{u})

section

variable {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (z : (X otimes Y).obj m)
/--
lemma `prod_map_fst` / 引理 `prod_map_fst`

English:
lemma prod_map_fst
  statement: dsimp% ((X otimes Y).map f z).1 = X.map f z.1
  proof: rfl

中文:
引理 prod_map_fst
  结论: dsimp% ((X otimes Y).map f z).1 = X.map f z.1
  证明: rfl
-/
@[simp high, grind =] lemma prod_map_fst : dsimp% ((X otimes Y).map f z).1 = X.map f z.1 := rfl
/--
lemma `prod_map_snd` / 引理 `prod_map_snd`

English:
lemma prod_map_snd
  statement: dsimp% ((X otimes Y).map f z).2 = Y.map f z.2
  proof: rfl

中文:
引理 prod_map_snd
  结论: dsimp% ((X otimes Y).map f z).2 = Y.map f z.2
  证明: rfl
-/
@[simp high, grind =] lemma prod_map_snd : dsimp% ((X otimes Y).map f z).2 = Y.map f z.2 := rfl

end

/--
lemma `prod_δ_fst` / 引理 `prod_δ_fst`

English:
lemma prod_δ_fst
  given: {n : Nat} (i : Fin (n + 2)) (z : (X otimes Y : SSet.{u}) _⦋n + 1⦌)
  proof: rfl

中文:
引理 prod_δ_fst
  条件: {n : 自然数} (i : 有限集 (n + 2)) (z : (X otimes Y : SSet.{u}) _⦋n + 1⦌)
  证明: rfl
-/
@[simp, grind =] lemma prod_δ_fst {n : Nat} (i : Fin (n + 2)) (z : (X otimes Y : SSet.{u}) _⦋n + 1⦌) :
    dsimp% ((X otimes Y).δ i z).1 = X.δ i z.1 := rfl

/--
lemma `prod_δ_snd` / 引理 `prod_δ_snd`

English:
lemma prod_δ_snd
  given: {n : Nat} (i : Fin (n + 2)) (z : (X otimes Y : SSet.{u}) _⦋n + 1⦌)
  proof: rfl

中文:
引理 prod_δ_snd
  条件: {n : 自然数} (i : 有限集 (n + 2)) (z : (X otimes Y : SSet.{u}) _⦋n + 1⦌)
  证明: rfl
-/
@[simp, grind =] lemma prod_δ_snd {n : Nat} (i : Fin (n + 2)) (z : (X otimes Y : SSet.{u}) _⦋n + 1⦌) :
    dsimp% ((X otimes Y).δ i z).2 = Y.δ i z.2 := rfl

/--
lemma `prod_σ_fst` / 引理 `prod_σ_fst`

English:
lemma prod_σ_fst
  given: {n : Nat} (i : Fin (n + 1)) (z : (X otimes Y : SSet.{u}) _⦋n⦌)
  proof: rfl

中文:
引理 prod_σ_fst
  条件: {n : 自然数} (i : 有限集 (n + 1)) (z : (X otimes Y : SSet.{u}) _⦋n⦌)
  证明: rfl
-/
@[simp, grind =] lemma prod_σ_fst {n : Nat} (i : Fin (n + 1)) (z : (X otimes Y : SSet.{u}) _⦋n⦌) :
    dsimp% ((X otimes Y).σ i z).1 = X.σ i z.1 := rfl

/--
lemma `prod_σ_snd` / 引理 `prod_σ_snd`

English:
lemma prod_σ_snd
  given: {n : Nat} (i : Fin (n + 1)) (z : (X otimes Y : SSet.{u}) _⦋n⦌)
  proof: rfl

中文:
引理 prod_σ_snd
  条件: {n : 自然数} (i : 有限集 (n + 1)) (z : (X otimes Y : SSet.{u}) _⦋n⦌)
  证明: rfl
-/
@[simp, grind =] lemma prod_σ_snd {n : Nat} (i : Fin (n + 1)) (z : (X otimes Y : SSet.{u}) _⦋n⦌) :
    dsimp% ((X otimes Y).σ i z).2 = Y.σ i z.2 := rfl

end

section

namespace Subcomplex

variable {X Y : SSet.{u}} (S : X.Subcomplex) (T : Y.Subcomplex)

/--
Definition of `unionProd` / `unionProd` 的定义

English:
definition unionProd
  signature: : (X otimes Y).Subcomplex
  body: ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

中文:
定义 unionProd
  签名: : (X otimes Y).子复形
  定义体: ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

Depends on / 依赖: S.prod, Subcomplex, X.Subcomplex
-/
def unionProd : (X otimes Y).Subcomplex := ((⊤ : X.Subcomplex).prod T) ⊔ (S.prod ⊤)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mem_unionProd_iff` / 引理 `mem_unionProd_iff`

English:
lemma mem_unionProd_iff
  given: {n : SimplexCategoryᵒᵖ} (x : (X otimes Y).obj n)
  proof: by
  dsimp [unionProd, Set.prod]
  cat_disch

中文:
引理 mem_unionProd_iff
  条件: {n : SimplexCategoryᵒᵖ} (x : (X otimes Y).obj n)
  证明: by
  dsimp [unionProd, Set.prod]
  cat_disch

Depends on / 依赖: Set.prod, cat_disch, unionProd
-/
lemma mem_unionProd_iff {n : SimplexCategoryᵒᵖ} (x : (X otimes Y).obj n) :
    dsimp% x in (unionProd S T).obj _ ↔ x.2 in T.obj _ ∨ x.1 in S.obj _ := by
  dsimp [unionProd, Set.prod]
  cat_disch

/--
lemma `top_prod_le_unionProd` / 引理 `top_prod_le_unionProd`

English:
lemma top_prod_le_unionProd
  statement: (⊤ : X.Subcomplex).prod T <= S.unionProd T
  proof: le_sup_left

中文:
引理 top_prod_le_unionProd
  结论: (⊤ : X.子复形).乘积 T <= S.unionProd T
  证明: le_sup_left

Depends on / 依赖: le_sup_left
-/
lemma top_prod_le_unionProd : (⊤ : X.Subcomplex).prod T <= S.unionProd T := le_sup_left

/--
lemma `prod_top_le_unionProd` / 引理 `prod_top_le_unionProd`

English:
lemma prod_top_le_unionProd
  statement: (S.prod ⊤) <= S.unionProd T
  proof: le_sup_right

中文:
引理 prod_top_le_unionProd
  结论: (S.乘积 ⊤) <= S.unionProd T
  证明: le_sup_right

Depends on / 依赖: le_sup_right
-/
lemma prod_top_le_unionProd : (S.prod ⊤) <= S.unionProd T := le_sup_right

/--
lemma `prod_le_unionProd` / 引理 `prod_le_unionProd`

English:
lemma prod_le_unionProd
  statement: S.prod T <= S.unionProd T
  proof: (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

中文:
引理 prod_le_unionProd
  结论: S.乘积 T <= S.unionProd T
  证明: (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

Depends on / 依赖: prod_le_prod_top, prod_top_le_unionProd
-/
lemma prod_le_unionProd : S.prod T <= S.unionProd T :=
  (prod_le_prod_top S T).trans (prod_top_le_unionProd S T)

/--
lemma `preimage_op_unionProd` / 引理 `preimage_op_unionProd`

English:
lemma preimage_op_unionProd
  proof: rfl

中文:
引理 preimage_op_unionProd
  证明: rfl
-/
lemma preimage_op_unionProd :
    (unionProd S T).op.preimage (Functor.LaxMonoidal.μ opFunctor _ _) =
      unionProd S.op T.op := rfl

/--
lemma `preimage_unionProd` / 引理 `preimage_unionProd`

English:
lemma preimage_unionProd
  given: {X' Y' : SSet.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y)
  proof: rfl

中文:
引理 preimage_unionProd
  条件: {X' Y' : SSet.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y)
  证明: rfl
-/
lemma preimage_unionProd {X' Y' : SSet.{u}} (f : X' ⟶ X) (g : Y' ⟶ Y) :
    (unionProd S T).preimage (f otimesₘ g) =
      unionProd (S.preimage f) (T.preimage g) := rfl

namespace unionProd

/--
Definition of `ι₁` / `ι₁` 的定义

English:
definition ι₁
  signature: : X otimes T ⟶ S.unionProd T
  body: lift (X ◁ T.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inl ⟨Set.mem_univ _, Subtype.coe_prop _⟩)

中文:
定义 ι₁
  签名: : X otimes T ⟶ S.unionProd T
  定义体: lift (X ◁ T.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inl ⟨Set.mem_univ _, Subtype.coe_prop _⟩)

Depends on / 依赖: Or.inl, Set.mem_univ, Subtype, Subtype.coe_prop, coe_prop, mem_univ
-/
noncomputable def ι₁ : X otimes T ⟶ S.unionProd T :=
  lift (X ◁ T.ι) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inl ⟨Set.mem_univ _, Subtype.coe_prop _⟩)

/--
Definition of `ι₂` / `ι₂` 的定义

English:
definition ι₂
  signature: : (S : SSet.{u}) otimes Y ⟶ (unionProd S T : SSet.{u})
  body: lift (S.ι ▷ Y) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inr ⟨Subtype.coe_prop _, Set.mem_univ _⟩)

@[reassoc (attr := simp)]

中文:
定义 ι₂
  签名: : (S : SSet.{u}) otimes Y ⟶ (unionProd S T : SSet.{u})
  定义体: lift (S.ι ▷ Y) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inr ⟨Subtype.coe_prop _, Set.mem_univ _⟩)

@[reassoc (attr := simp)]

Depends on / 依赖: Or.inr, Set.mem_univ, Subtype, Subtype.coe_prop, coe_prop, mem_univ
-/
noncomputable def ι₂ : (S : SSet.{u}) otimes Y ⟶ (unionProd S T : SSet.{u}) :=
  lift (S.ι ▷ Y) (by
    rintro m _ ⟨⟨y₁, y₂⟩, ⟨⟩⟩
    exact Or.inr ⟨Subtype.coe_prop _, Set.mem_univ _⟩)

@[reassoc (attr := simp)]
/--
lemma `ι₁_ι` / 引理 `ι₁_ι`

English:
lemma ι₁_ι
  statement: ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι₁_ι
  结论: ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι₁_ι : ι₁ S T ≫ (unionProd S T).ι = X ◁ T.ι := rfl

@[reassoc (attr := simp)]
/--
lemma `ι₂_ι` / 引理 `ι₂_ι`

English:
lemma ι₂_ι
  statement: ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y
  proof: rfl

中文:
引理 ι₂_ι
  结论: ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y
  证明: rfl
-/
lemma ι₂_ι : ι₂ S T ≫ (unionProd S T).ι = S.ι ▷ Y := rfl

/--
lemma `bicartSq` / 引理 `bicartSq`

English:
lemma bicartSq
  statement: BicartSq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  proof: rfl
  inf_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, Set.ofPred]
    tauto

中文:
引理 bicartSq
  结论: BicartSq (S.乘积 T) ((⊤ : X.子复形).乘积 T) (S.乘积 ⊤) (unionProd S T) where
  证明: rfl
  inf_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, Set.ofPred]
    tauto
-/
lemma bicartSq : BicartSq (S.prod T) ((⊤ : X.Subcomplex).prod T) (S.prod ⊤) (unionProd S T) where
  sup_eq := rfl
  inf_eq := by
    ext n ⟨x, y⟩
    change _ ∧ _ ↔ _
    simp [prod, Set.prod, Membership.mem, Set.Mem, Set.ofPred]
    tauto

/--
lemma `isPushout` / 引理 `isPushout`

English:
lemma isPushout
  statement: IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
  proof: (bicartSq S T).isPushout.of_iso (S.prodIso T)
    (prodIso _ _ ≪≫ whiskerRightIso (topIso X) _)
    (prodIso _ _ ≪≫ whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

中文:
引理 isPushout
  结论: 是推出 (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
  证明: (bicartSq S T).isPushout.of_iso (S.prodIso T)
    (prodIso _ _ ≪≫ whiskerRightIso (topIso X) _)
    (prodIso _ _ ≪≫ whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

Depends on / 依赖: Iso.refl, S.prodIso, bicartSq, isPushout, isPushout.of_iso, of_iso, prodIso, topIso, whiskerLeftIso, whiskerRightIso
-/
lemma isPushout : IsPushout (S.ι ▷ (T : SSet)) ((S : SSet) ◁ T.ι)
    (unionProd.ι₁ S T) (unionProd.ι₂ S T) :=
  (bicartSq S T).isPushout.of_iso (S.prodIso T)
    (prodIso _ _ ≪≫ whiskerRightIso (topIso X) _)
    (prodIso _ _ ≪≫ whiskerLeftIso _ (topIso Y))
    (Iso.refl _) rfl rfl rfl rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `preimage_β_hom` / 引理 `preimage_β_hom`

English:
lemma preimage_β_hom
  statement: (unionProd S T).preimage (β_ _ _).hom = unionProd T S
  proof: by
  ext n ⟨x, y⟩
  dsimp
  simp only [mem_unionProd_iff, preimage_obj, Monoidal.tensorObj_obj,
    dsimp% Set.mem_preimage (f := (β_ Y X).hom.app n)]
  tauto

@[simp]

中文:
引理 preimage_β_hom
  结论: (unionProd S T).原像 (β_ _ _).hom = unionProd T S
  证明: by
  ext n ⟨x, y⟩
  dsimp
  simp only [mem_unionProd_iff, preimage_obj, Monoidal.tensorObj_obj,
    dsimp% Set.mem_preimage (f := (β_ Y X).hom.app n)]
  tauto

@[simp]

Depends on / 依赖: Monoidal, Monoidal.tensorObj_obj, Set.mem_preimage, hom.app, mem_preimage, mem_unionProd_iff, preimage_obj, tensorObj_obj
-/
lemma preimage_β_hom : (unionProd S T).preimage (β_ _ _).hom = unionProd T S := by
  ext n ⟨x, y⟩
  dsimp
  simp only [mem_unionProd_iff, preimage_obj, Monoidal.tensorObj_obj,
    dsimp% Set.mem_preimage (f := (β_ Y X).hom.app n)]
  tauto

@[simp]
/--
lemma `preimage_β_inv` / 引理 `preimage_β_inv`

English:
lemma preimage_β_inv
  statement: (unionProd S T).preimage (β_ _ _).inv = unionProd T S
  proof: by
  apply preimage_β_hom

@[simp]

中文:
引理 preimage_β_inv
  结论: (unionProd S T).原像 (β_ _ _).inv = unionProd T S
  证明: by
  apply preimage_β_hom

@[simp]
-/
lemma preimage_β_inv : (unionProd S T).preimage (β_ _ _).inv = unionProd T S := by
  apply preimage_β_hom

@[simp]
/--
lemma `image_β_hom` / 引理 `image_β_hom`

English:
lemma image_β_hom
  statement: (unionProd S T).image (β_ _ _).hom = unionProd T S
  proof: by
  rw [← preimage_β_hom]; rw [preimage_image_of_isIso]

@[simp]

中文:
引理 image_β_hom
  结论: (unionProd S T).像 (β_ _ _).hom = unionProd T S
  证明: by
  rw [← preimage_β_hom]; rw [preimage_image_of_isIso]

@[simp]

Depends on / 依赖: preimage_image_of_isIso
-/
lemma image_β_hom : (unionProd S T).image (β_ _ _).hom = unionProd T S := by
  rw [← preimage_β_hom]; rw [preimage_image_of_isIso]

@[simp]
/--
lemma `image_β_inv` / 引理 `image_β_inv`

English:
lemma image_β_inv
  statement: (unionProd S T).image (β_ _ _).inv = unionProd T S
  proof: by
  apply image_β_hom

中文:
引理 image_β_inv
  结论: (unionProd S T).像 (β_ _ _).inv = unionProd T S
  证明: by
  apply image_β_hom
-/
lemma image_β_inv : (unionProd S T).image (β_ _ _).inv = unionProd T S := by
  apply image_β_hom

/-- The isomorphism `unionProd S T ≅ unionProd T S` as simplicial sets. -/
@[simps]
/--
Definition of `symmIso` / `symmIso` 的定义

English:
definition symmIso
  signature: : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  body: lift ((unionProd S T).ι ≫ (β_ _ _).hom) (by simp [range_comp])
  inv := lift ((unionProd T S).ι ≫ (β_ _ _).hom) (by simp [range_comp])

中文:
定义 symmIso
  签名: : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  定义体: lift ((unionProd S T).ι ≫ (β_ _ _).hom) (by simp [range_comp])
  inv := lift ((unionProd T S).ι ≫ (β_ _ _).hom) (by simp [range_comp])

Depends on / 依赖: range_comp, unionProd
-/
noncomputable def symmIso : (unionProd S T : SSet) ≅ (unionProd T S : SSet) where
  hom := lift ((unionProd S T).ι ≫ (β_ _ _).hom) (by simp [range_comp])
  inv := lift ((unionProd T S).ι ≫ (β_ _ _).hom) (by simp [range_comp])

end unionProd

end Subcomplex

end

namespace Truncated

variable (n : Nat)

open MonoidalCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (truncation.{u} n).Monoidal
  body: inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj _).Monoidal

中文:
实例 :
  签名: (truncation.{u} n).幺半群
  定义体: inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj _).Monoidal

Depends on / 依赖: Functor, Functor.whiskeringLeft, Monoidal, whiskeringLeft
-/
instance : (truncation.{u} n).Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj _).Monoidal

variable {n} {X Y : Truncated.{u} n}

@[simp]
/--
lemma `tensor_map_apply_fst` / 引理 `tensor_map_apply_fst`

English:
lemma tensor_map_apply_fst
  statement: {d e : (SimplexCategory.Truncated n)ᵒᵖ}
  proof: rfl

@[simp]

中文:
引理 tensor_map_apply_fst
  结论: {d e : (单纯形范畴.Truncated n)ᵒᵖ}
  证明: rfl

@[simp]
-/
lemma tensor_map_apply_fst {d e : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : d ⟶ e) (x : (X otimes Y : Truncated _).obj d) :
    dsimp% ((X otimes Y : Truncated _).map f x).1 = X.map f x.1 := rfl

@[simp]
/--
lemma `tensor_map_apply_snd` / 引理 `tensor_map_apply_snd`

English:
lemma tensor_map_apply_snd
  statement: {d e : (SimplexCategory.Truncated n)ᵒᵖ}
  proof: rfl

中文:
引理 tensor_map_apply_snd
  结论: {d e : (单纯形范畴.Truncated n)ᵒᵖ}
  证明: rfl
-/
lemma tensor_map_apply_snd {d e : (SimplexCategory.Truncated n)ᵒᵖ}
    (f : d ⟶ e) (x : (X otimes Y : Truncated _).obj d) :
    dsimp% ((X otimes Y : Truncated _).map f x).2 = Y.map f x.2 := rfl

end Truncated

end SSet
