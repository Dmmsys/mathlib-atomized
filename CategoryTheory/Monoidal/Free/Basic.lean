/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The free monoidal category over a type

Given a type `C`, the free monoidal category over `C` has as objects formal expressions built from
(formal) tensor products of terms of `C` and a formal unit. Its morphisms are compositions and
tensor products of identities, unitors and associators.

In this file, we construct the free monoidal category and prove that it is a monoidal category. If
`D` is a monoidal category, we construct the functor `FreeMonoidalCategory C ⥤ D` associated to
a function `C → D`.

The free monoidal category has two important properties: it is a groupoid and it is thin. The former
is obvious from the construction, and the latter is what is commonly known as the monoidal coherence
theorem. Both of these properties are proved in the file `Coherence.lean`.

-/

@[expose] public section


universe v' u u'

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u}

section

variable (C)

-- Don't generate unnecessary `sizeOf_spec` or `injEq` lemmas
-- which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/--
Inductive type `FreeMonoidalCategory` / 归纳类型 `FreeMonoidalCategory`

English:
inductive FreeMonoidalCategory
  parameters: : Type u
  constructors (3):
    - of: C -> FreeMonoidalCategory
    - unit: FreeMonoidalCategory
    - tensor: FreeMonoidalCategory -> FreeMonoidalCategory -> FreeMonoidalCategory

中文:
归纳类型 FreeMonoidal范畴
  参数: : 类型u
  构造子 (3 个):
    - of: C -> FreeMonoidal范畴
    - unit: FreeMonoidal范畴
    - tensor: FreeMonoidal范畴 -> FreeMonoidal范畴 -> FreeMonoidal范畴
-/
inductive FreeMonoidalCategory : Type u
  | of : C -> FreeMonoidalCategory
  | unit : FreeMonoidalCategory
  | tensor : FreeMonoidalCategory -> FreeMonoidalCategory -> FreeMonoidalCategory
  deriving Inhabited

end

local notation "F" => FreeMonoidalCategory

namespace FreeMonoidalCategory

/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : F C -> F C -> Type u
  constructors (11):
    - id: (X) : Hom X X
    - α_hom: (X Y Z : F C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
    - α_inv: (X Y Z : F C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
    - l_hom: (X) : Hom (unit.tensor X) X
    - l_inv: (X) : Hom X (unit.tensor X)
    - ρ_hom: (X : F C) : Hom (X.tensor unit) X
    - ρ_inv: (X : F C) : Hom X (X.tensor unit)
    - comp: {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
    - whiskerLeft: (X : F C) {Y₁ Y₂} (f : Hom Y₁ Y₂) : Hom (X.tensor Y₁) (X.tensor Y₂)
    - whiskerRight: {X₁ X₂} (f : Hom X₁ X₂) (Y : F C) : Hom (X₁.tensor Y) (X₂.tensor Y)
    - tensor: {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

中文:
归纳类型 态射
  参数: : F C -> F C -> 类型u
  构造子 (11 个):
    - id: (X) : 态射 X X
    - α_hom: (X Y Z : F C) : 态射 ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
    - α_inv: (X Y Z : F C) : 态射 (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
    - l_hom: (X) : 态射 (unit.tensor X) X
    - l_inv: (X) : 态射 X (unit.tensor X)
    - ρ_hom: (X : F C) : 态射 (X.tensor unit) X
    - ρ_inv: (X : F C) : 态射 X (X.tensor unit)
    - comp: {X Y Z} (f : 态射 X Y) (g : 态射 Y Z) : 态射 X Z
    - whiskerLeft: (X : F C) {Y₁ Y₂} (f : 态射 Y₁ Y₂) : 态射 (X.tensor Y₁) (X.tensor Y₂)
    - whiskerRight: {X₁ X₂} (f : 态射 X₁ X₂) (Y : F C) : 态射 (X₁.tensor Y) (X₂.tensor Y)
    - tensor: {W X Y Z} (f : 态射 W Y) (g : 态射 X Z) : 态射 (W.tensor X) (Y.tensor Z)
-/
inductive Hom : F C -> F C -> Type u
  | id (X) : Hom X X
  | α_hom (X Y Z : F C) : Hom ((X.tensor Y).tensor Z) (X.tensor (Y.tensor Z))
  | α_inv (X Y Z : F C) : Hom (X.tensor (Y.tensor Z)) ((X.tensor Y).tensor Z)
  | l_hom (X) : Hom (unit.tensor X) X
  | l_inv (X) : Hom X (unit.tensor X)
  | ρ_hom (X : F C) : Hom (X.tensor unit) X
  | ρ_inv (X : F C) : Hom X (X.tensor unit)
  | comp {X Y Z} (f : Hom X Y) (g : Hom Y Z) : Hom X Z
  | whiskerLeft (X : F C) {Y₁ Y₂} (f : Hom Y₁ Y₂) : Hom (X.tensor Y₁) (X.tensor Y₂)
  | whiskerRight {X₁ X₂} (f : Hom X₁ X₂) (Y : F C) : Hom (X₁.tensor Y) (X₂.tensor Y)
  | tensor {W X Y Z} (f : Hom W Y) (g : Hom X Z) : Hom (W.tensor X) (Y.tensor Z)

local infixr:10 " ⟶ᵐ " => Hom

/--
Inductive type `HomEquiv` / 归纳类型 `HomEquiv`

English:
inductive HomEquiv
  parameters: : forall {X Y : F C}, (X ⟶ᵐ Y) -> (X ⟶ᵐ Y) -> Prop
  constructors (26):
    - refl: {X Y} (f : X ⟶ᵐ Y) : HomEquiv f f
    - symm: {X Y} (f g : X ⟶ᵐ Y) : HomEquiv f g -> HomEquiv g f
    - trans: {X Y} {f g h : X ⟶ᵐ Y} : HomEquiv f g -> HomEquiv g h -> HomEquiv f h
    - comp: {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} : HomEquiv f f' -> HomEquiv g g' -> HomEquiv (f.comp g) (f'.comp g')
    - whiskerLeft: (X) {Y Z} (f f' : Y ⟶ᵐ Z) : HomEquiv f f' -> HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
    - whiskerRight: {Y Z} (f f' : Y ⟶ᵐ Z) (X) : HomEquiv f f' -> HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
    - tensor: {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} : HomEquiv f f' -> HomEquiv g g' -> HomEquiv (f.tensor g) (f'.tensor g')
    - tensorHom_def: {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) : HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
    - comp_id: {X Y} (f : X ⟶ᵐ Y) : HomEquiv (f.comp (Hom.id _)) f
    - id_comp: {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((Hom.id _).comp f) f
    - assoc: {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) : HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
    - id_tensorHom_id: {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
    - tensorHom_comp_tensorHom: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) : HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
    - whiskerLeft_id: (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
    - id_whiskerRight: (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
    - α_hom_inv: {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
    - α_inv_hom: {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
    - associator_naturality: {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) : HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃)) ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
    - ρ_hom_inv: {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
    - ρ_inv_hom: {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
    - ρ_naturality: {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
    - l_hom_inv: {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
    - l_inv_hom: {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
    - l_naturality: {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
    - pentagon: {W X Y Z} : HomEquiv (((Hom.α_hom W X Y).whiskerRight Z).comp ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W))) ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
    - triangle: {X Y} : HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X)) ((Hom.ρ_hom X).whiskerRight Y)

中文:
归纳类型 态射等价
  参数: : 对任意 {X Y : F C}, (X ⟶ᵐ Y) -> (X ⟶ᵐ Y) -> 命题
  构造子 (26 个):
    - refl: {X Y} (f : X ⟶ᵐ Y) : 态射等价 f f
    - symm: {X Y} (f g : X ⟶ᵐ Y) : 态射等价 f g -> 态射等价 g f
    - trans: {X Y} {f g h : X ⟶ᵐ Y} : 态射等价 f g -> 态射等价 g h -> 态射等价 f h
    - comp: {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} : 态射等价 f f' -> 态射等价 g g' -> 态射等价 (f.comp g) (f'.comp g')
    - whiskerLeft: (X) {Y Z} (f f' : Y ⟶ᵐ Z) : 态射等价 f f' -> 态射等价 (f.whiskerLeft X) (f'.whiskerLeft X)
    - whiskerRight: {Y Z} (f f' : Y ⟶ᵐ Z) (X) : 态射等价 f f' -> 态射等价 (f.whiskerRight X) (f'.whiskerRight X)
    - tensor: {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} : 态射等价 f f' -> 态射等价 g g' -> 态射等价 (f.tensor g) (f'.tensor g')
    - tensorHom_def: {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) : 态射等价 (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
    - comp_id: {X Y} (f : X ⟶ᵐ Y) : 态射等价 (f.comp (态射.id _)) f
    - id_comp: {X Y} (f : X ⟶ᵐ Y) : 态射等价 ((态射.id _).comp f) f
    - assoc: {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) : 态射等价 ((f.comp g).comp h) (f.comp (g.comp h))
    - id_tensorHom_id: {X Y} : 态射等价 ((态射.id X).tensor (态射.id Y)) (态射.id _)
    - tensorHom_comp_tensorHom: {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) : 态射等价 ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
    - whiskerLeft_id: (X Y) : 态射等价 ((态射.id Y).whiskerLeft X) (态射.id (X.tensor Y))
    - id_whiskerRight: (X Y) : 态射等价 ((态射.id X).whiskerRight Y) (态射.id (X.tensor Y))
    - α_hom_inv: {X Y Z} : 态射等价 ((态射.α_hom X Y Z).comp (态射.α_inv X Y Z)) (态射.id _)
    - α_inv_hom: {X Y Z} : 态射等价 ((态射.α_inv X Y Z).comp (态射.α_hom X Y Z)) (态射.id _)
    - associator_naturality: {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) : 态射等价 (((f₁.tensor f₂).tensor f₃).comp (态射.α_hom Y₁ Y₂ Y₃)) ((态射.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
    - ρ_hom_inv: {X} : 态射等价 ((态射.ρ_hom X).comp (态射.ρ_inv X)) (态射.id _)
    - ρ_inv_hom: {X} : 态射等价 ((态射.ρ_inv X).comp (态射.ρ_hom X)) (态射.id _)
    - ρ_naturality: {X Y} (f : X ⟶ᵐ Y) : 态射等价 ((f.whiskerRight unit).comp (态射.ρ_hom Y)) ((态射.ρ_hom X).comp f)
    - l_hom_inv: {X} : 态射等价 ((态射.l_hom X).comp (态射.l_inv X)) (态射.id _)
    - l_inv_hom: {X} : 态射等价 ((态射.l_inv X).comp (态射.l_hom X)) (态射.id _)
    - l_naturality: {X Y} (f : X ⟶ᵐ Y) : 态射等价 ((f.whiskerLeft unit).comp (态射.l_hom Y)) ((态射.l_hom X).comp f)
    - pentagon: {W X Y Z} : 态射等价 (((态射.α_hom W X Y).whiskerRight Z).comp ((态射.α_hom W (X.tensor Y) Z).comp ((态射.α_hom X Y Z).whiskerLeft W))) ((态射.α_hom (W.tensor X) Y Z).comp (态射.α_hom W X (Y.tensor Z)))
    - triangle: {X Y} : 态射等价 ((态射.α_hom X unit Y).comp ((态射.l_hom Y).whiskerLeft X)) ((态射.ρ_hom X).whiskerRight Y)
-/
inductive HomEquiv : forall {X Y : F C}, (X ⟶ᵐ Y) -> (X ⟶ᵐ Y) -> Prop
  | refl {X Y} (f : X ⟶ᵐ Y) : HomEquiv f f
  | symm {X Y} (f g : X ⟶ᵐ Y) : HomEquiv f g -> HomEquiv g f
  | trans {X Y} {f g h : X ⟶ᵐ Y} : HomEquiv f g -> HomEquiv g h -> HomEquiv f h
  | comp {X Y Z} {f f' : X ⟶ᵐ Y} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' -> HomEquiv g g' -> HomEquiv (f.comp g) (f'.comp g')
  | whiskerLeft (X) {Y Z} (f f' : Y ⟶ᵐ Z) :
      HomEquiv f f' -> HomEquiv (f.whiskerLeft X) (f'.whiskerLeft X)
  | whiskerRight {Y Z} (f f' : Y ⟶ᵐ Z) (X) :
      HomEquiv f f' -> HomEquiv (f.whiskerRight X) (f'.whiskerRight X)
  | tensor {W X Y Z} {f f' : W ⟶ᵐ X} {g g' : Y ⟶ᵐ Z} :
      HomEquiv f f' -> HomEquiv g g' -> HomEquiv (f.tensor g) (f'.tensor g')
  | tensorHom_def {X₁ Y₁ X₂ Y₂} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
      HomEquiv (f.tensor g) ((f.whiskerRight X₂).comp (g.whiskerLeft Y₁))
  | comp_id {X Y} (f : X ⟶ᵐ Y) : HomEquiv (f.comp (Hom.id _)) f
  | id_comp {X Y} (f : X ⟶ᵐ Y) : HomEquiv ((Hom.id _).comp f) f
  | assoc {X Y U V : F C} (f : X ⟶ᵐ U) (g : U ⟶ᵐ V) (h : V ⟶ᵐ Y) :
      HomEquiv ((f.comp g).comp h) (f.comp (g.comp h))
  | id_tensorHom_id {X Y} : HomEquiv ((Hom.id X).tensor (Hom.id Y)) (Hom.id _)
  | tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : F C} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂)
      (g₁ : Y₁ ⟶ᵐ Z₁) (g₂ : Y₂ ⟶ᵐ Z₂) :
    HomEquiv ((f₁.tensor f₂).comp (g₁.tensor g₂)) ((f₁.comp g₁).tensor (f₂.comp g₂))
  | whiskerLeft_id (X Y) : HomEquiv ((Hom.id Y).whiskerLeft X) (Hom.id (X.tensor Y))
  | id_whiskerRight (X Y) : HomEquiv ((Hom.id X).whiskerRight Y) (Hom.id (X.tensor Y))
  | α_hom_inv {X Y Z} : HomEquiv ((Hom.α_hom X Y Z).comp (Hom.α_inv X Y Z)) (Hom.id _)
  | α_inv_hom {X Y Z} : HomEquiv ((Hom.α_inv X Y Z).comp (Hom.α_hom X Y Z)) (Hom.id _)
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁ : X₁ ⟶ᵐ Y₁) (f₂ : X₂ ⟶ᵐ Y₂) (f₃ : X₃ ⟶ᵐ Y₃) :
      HomEquiv (((f₁.tensor f₂).tensor f₃).comp (Hom.α_hom Y₁ Y₂ Y₃))
        ((Hom.α_hom X₁ X₂ X₃).comp (f₁.tensor (f₂.tensor f₃)))
  | ρ_hom_inv {X} : HomEquiv ((Hom.ρ_hom X).comp (Hom.ρ_inv X)) (Hom.id _)
  | ρ_inv_hom {X} : HomEquiv ((Hom.ρ_inv X).comp (Hom.ρ_hom X)) (Hom.id _)
  | ρ_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerRight unit).comp (Hom.ρ_hom Y)) ((Hom.ρ_hom X).comp f)
  | l_hom_inv {X} : HomEquiv ((Hom.l_hom X).comp (Hom.l_inv X)) (Hom.id _)
  | l_inv_hom {X} : HomEquiv ((Hom.l_inv X).comp (Hom.l_hom X)) (Hom.id _)
  | l_naturality {X Y} (f : X ⟶ᵐ Y) :
      HomEquiv ((f.whiskerLeft unit).comp (Hom.l_hom Y)) ((Hom.l_hom X).comp f)
  | pentagon {W X Y Z} :
      HomEquiv
        (((Hom.α_hom W X Y).whiskerRight Z).comp
          ((Hom.α_hom W (X.tensor Y) Z).comp ((Hom.α_hom X Y Z).whiskerLeft W)))
        ((Hom.α_hom (W.tensor X) Y Z).comp (Hom.α_hom W X (Y.tensor Z)))
  | triangle {X Y} :
      HomEquiv ((Hom.α_hom X unit Y).comp ((Hom.l_hom Y).whiskerLeft X))
        ((Hom.ρ_hom X).whiskerRight Y)

/--
Instance `setoidHom` / 实例 `setoidHom`

English:
instance setoidHom
  signature: (X Y : F C)
  body: ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

中文:
实例 setoidHom
  签名: (X Y : F C)
  定义体: ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

Depends on / 依赖: HomEquiv, HomEquiv.refl, HomEquiv.symm, HomEquiv.trans
-/
instance setoidHom (X Y : F C) : Setoid (X ⟶ᵐ Y) :=
  ⟨HomEquiv, ⟨HomEquiv.refl, HomEquiv.symm _ _, HomEquiv.trans⟩⟩

section

open FreeMonoidalCategory.HomEquiv

/--
Instance `categoryFreeMonoidalCategory` / 实例 `categoryFreeMonoidalCategory`

English:
instance categoryFreeMonoidalCategory
  signature: : Category.{u} (F C) where
  body: Quotient (FreeMonoidalCategory.setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg => HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by

中文:
实例 categoryFreeMonoidalCategory
  签名: : 范畴.{u} (F C) where
  定义体: Quotient (FreeMonoidalCategory.setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg => HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by

Depends on / 依赖: FreeMonoidalCategory, FreeMonoidalCategory.setoidHom, Quotient, setoidHom
-/
instance categoryFreeMonoidalCategory : Category.{u} (F C) where
  Hom X Y := Quotient (FreeMonoidalCategory.setoidHom X Y)
  id X := ⟦Hom.id X⟧
  comp := Quotient.map₂ Hom.comp (fun _ _ hf _ _ hg => HomEquiv.comp hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (assoc f g h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory (F C)
  body: FreeMonoidalCategory.tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg => HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f => Hom.whiskerLeft X f) (fun f f' => .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f => Hom.whiskerRight f Y) (fun f f' => .whisk

中文:
实例 :
  签名: 幺半群范畴 (F C)
  定义体: FreeMonoidalCategory.tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg => HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f => Hom.whiskerLeft X f) (fun f f' => .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f => Hom.whiskerRight f Y) (fun f f' => .whisk

Depends on / 依赖: FreeMonoidalCategory, FreeMonoidalCategory.tensor, tensor
-/
instance : MonoidalCategory (F C) where
  tensorObj X Y := FreeMonoidalCategory.tensor X Y
  tensorHom := Quotient.map₂ Hom.tensor (fun _ _ hf _ _ hg => HomEquiv.tensor hf hg)
  whiskerLeft X _ _ f := Quot.map (fun f => Hom.whiskerLeft X f) (fun f f' => .whiskerLeft X f f') f
  whiskerRight f Y := Quot.map (fun f => Hom.whiskerRight f Y) (fun f f' => .whiskerRight f f' Y) f
  tensorHom_def {W X Y Z} := by
    rintro ⟨f⟩ ⟨g⟩
    exact Quotient.sound (tensorHom_def _ _)
  id_tensorHom_id _ _ := Quot.sound id_tensorHom_id
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (tensorHom_comp_tensorHom _ _ _ _)
  whiskerLeft_id X Y := Quot.sound (HomEquiv.whiskerLeft_id X Y)
  id_whiskerRight X Y := Quot.sound (HomEquiv.id_whiskerRight X Y)
  tensorUnit := FreeMonoidalCategory.unit
  associator X Y Z :=
    ⟨⟦Hom.α_hom X Y Z⟧, ⟦Hom.α_inv X Y Z⟧, Quotient.sound α_hom_inv, Quotient.sound α_inv_hom⟩
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} := by
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
    exact Quotient.sound (associator_naturality _ _ _)
  leftUnitor X := ⟨⟦Hom.l_hom X⟧, ⟦Hom.l_inv X⟧, Quotient.sound l_hom_inv, Quotient.sound l_inv_hom⟩
  leftUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact Quotient.sound (l_naturality _)
  rightUnitor X :=
    ⟨⟦Hom.ρ_hom X⟧, ⟦Hom.ρ_inv X⟧, Quotient.sound ρ_hom_inv, Quotient.sound ρ_inv_hom⟩
  rightUnitor_naturality {X Y} := by
    rintro ⟨f⟩
    exact Quotient.sound (ρ_naturality _)
  pentagon _ _ _ _ := Quotient.sound pentagon
  triangle _ _ := Quotient.sound triangle

@[simp]
/--
theorem `mk_comp` / 定理 `mk_comp`

English:
theorem mk_comp
  given: {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z)
  proof: rfl

@[simp]

中文:
定理 mk_comp
  条件: {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z)
  证明: rfl

@[simp]
-/
theorem mk_comp {X Y Z : F C} (f : X ⟶ᵐ Y) (g : Y ⟶ᵐ Z) :
    ⟦f.comp g⟧ = @CategoryStruct.comp (F C) _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
/--
theorem `mk_tensor` / 定理 `mk_tensor`

English:
theorem mk_tensor
  given: {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂)
  proof: rfl

@[simp]

中文:
定理 mk_tensor
  条件: {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂)
  证明: rfl

@[simp]
-/
theorem mk_tensor {X₁ Y₁ X₂ Y₂ : F C} (f : X₁ ⟶ᵐ Y₁) (g : X₂ ⟶ᵐ Y₂) :
    ⟦f.tensor g⟧ = @MonoidalCategory.tensorHom (F C) _ _ _ _ _ _ ⟦f⟧ ⟦g⟧ :=
  rfl

@[simp]
/--
theorem `mk_whiskerLeft` / 定理 `mk_whiskerLeft`

English:
theorem mk_whiskerLeft
  given: (X : F C) {Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂)
  proof: rfl

@[simp]

中文:
定理 mk_whiskerLeft
  条件: (X : F C) {Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂)
  证明: rfl

@[simp]

Depends on / 依赖: Unique
-/
theorem mk_whiskerLeft (X : F C) {Y₁ Y₂ : F C} (f : Y₁ ⟶ᵐ Y₂) :
    ⟦f.whiskerLeft X⟧ = MonoidalCategory.whiskerLeft (C := F C) (X := X) (f := ⟦f⟧) :=
  rfl

@[simp]
/--
theorem `mk_whiskerRight` / 定理 `mk_whiskerRight`

English:
theorem mk_whiskerRight
  given: {X₁ X₂ : F C} (f : X₁ ⟶ᵐ X₂) (Y : F C)
  proof: rfl

@[simp]

中文:
定理 mk_whiskerRight
  条件: {X₁ X₂ : F C} (f : X₁ ⟶ᵐ X₂) (Y : F C)
  证明: rfl

@[simp]
-/
theorem mk_whiskerRight {X₁ X₂ : F C} (f : X₁ ⟶ᵐ X₂) (Y : F C) :
    ⟦f.whiskerRight Y⟧ = MonoidalCategory.whiskerRight (C := F C) (f := ⟦f⟧) (Y := Y) :=
  rfl

@[simp]
/--
theorem `mk_id` / 定理 `mk_id`

English:
theorem mk_id
  given: {X : F C}
  statement: ⟦Hom.id X⟧ = 𝟙 X
  proof: rfl

@[simp]

中文:
定理 mk_id
  条件: {X : F C}
  结论: ⟦态射.id X⟧ = 𝟙 X
  证明: rfl

@[simp]
-/
theorem mk_id {X : F C} : ⟦Hom.id X⟧ = 𝟙 X :=
  rfl

@[simp]
/--
theorem `mk_α_hom` / 定理 `mk_α_hom`

English:
theorem mk_α_hom
  given: {X Y Z : F C}
  statement: ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom
  proof: rfl

@[simp]

中文:
定理 mk_α_hom
  条件: {X Y Z : F C}
  结论: ⟦态射.α_hom X Y Z⟧ = (α_ X Y Z).hom
  证明: rfl

@[simp]
-/
theorem mk_α_hom {X Y Z : F C} : ⟦Hom.α_hom X Y Z⟧ = (α_ X Y Z).hom :=
  rfl

@[simp]
/--
theorem `mk_α_inv` / 定理 `mk_α_inv`

English:
theorem mk_α_inv
  given: {X Y Z : F C}
  statement: ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv
  proof: rfl

@[simp]

中文:
定理 mk_α_inv
  条件: {X Y Z : F C}
  结论: ⟦态射.α_inv X Y Z⟧ = (α_ X Y Z).inv
  证明: rfl

@[simp]
-/
theorem mk_α_inv {X Y Z : F C} : ⟦Hom.α_inv X Y Z⟧ = (α_ X Y Z).inv :=
  rfl

@[simp]
/--
theorem `mk_ρ_hom` / 定理 `mk_ρ_hom`

English:
theorem mk_ρ_hom
  given: {X : F C}
  statement: ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom
  proof: rfl

@[simp]

中文:
定理 mk_ρ_hom
  条件: {X : F C}
  结论: ⟦态射.ρ_hom X⟧ = (ρ_ X).hom
  证明: rfl

@[simp]
-/
theorem mk_ρ_hom {X : F C} : ⟦Hom.ρ_hom X⟧ = (ρ_ X).hom :=
  rfl

@[simp]
/--
theorem `mk_ρ_inv` / 定理 `mk_ρ_inv`

English:
theorem mk_ρ_inv
  given: {X : F C}
  statement: ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv
  proof: rfl

@[simp]

中文:
定理 mk_ρ_inv
  条件: {X : F C}
  结论: ⟦态射.ρ_inv X⟧ = (ρ_ X).inv
  证明: rfl

@[simp]
-/
theorem mk_ρ_inv {X : F C} : ⟦Hom.ρ_inv X⟧ = (ρ_ X).inv :=
  rfl

@[simp]
/--
theorem `mk_l_hom` / 定理 `mk_l_hom`

English:
theorem mk_l_hom
  given: {X : F C}
  statement: ⟦Hom.l_hom X⟧ = (fun_ X).hom
  proof: rfl

@[simp]

中文:
定理 mk_l_hom
  条件: {X : F C}
  结论: ⟦态射.l_hom X⟧ = (fun_ X).hom
  证明: rfl

@[simp]
-/
theorem mk_l_hom {X : F C} : ⟦Hom.l_hom X⟧ = (fun_ X).hom :=
  rfl

@[simp]
/--
theorem `mk_l_inv` / 定理 `mk_l_inv`

English:
theorem mk_l_inv
  given: {X : F C}
  statement: ⟦Hom.l_inv X⟧ = (fun_ X).inv
  proof: rfl

@[simp]

中文:
定理 mk_l_inv
  条件: {X : F C}
  结论: ⟦态射.l_inv X⟧ = (fun_ X).inv
  证明: rfl

@[simp]
-/
theorem mk_l_inv {X : F C} : ⟦Hom.l_inv X⟧ = (fun_ X).inv :=
  rfl

@[simp]
/--
theorem `tensor_eq_tensor` / 定理 `tensor_eq_tensor`

English:
theorem tensor_eq_tensor
  given: {X Y : F C}
  statement: X.tensor Y = X otimes Y
  proof: rfl

@[simp]

中文:
定理 tensor_eq_tensor
  条件: {X Y : F C}
  结论: X.tensor Y = X otimes Y
  证明: rfl

@[simp]
-/
theorem tensor_eq_tensor {X Y : F C} : X.tensor Y = X otimes Y :=
  rfl

@[simp]
/--
theorem `unit_eq_unit` / 定理 `unit_eq_unit`

English:
theorem unit_eq_unit
  statement: FreeMonoidalCategory.unit = 𝟙_ (F C)
  proof: rfl

中文:
定理 unit_eq_unit
  结论: FreeMonoidal范畴.unit = 𝟙_ (F C)
  证明: rfl

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.Hom.id
-/
theorem unit_eq_unit : FreeMonoidalCategory.unit = 𝟙_ (F C) :=
  rfl

/-- The abbreviation for `⟦f⟧`. -/
/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {X Y : F C} (f : X ⟶ᵐ Y)
  body: ⟦f⟧

中文:
缩写 homMk
  签名: {X Y : F C} (f : X ⟶ᵐ Y)
  定义体: ⟦f⟧

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.Hom.comp
-/
abbrev homMk {X Y : F C} (f : X ⟶ᵐ Y) : X ⟶ Y := ⟦f⟧

/--
theorem `Hom.inductionOn` / 定理 `Hom.inductionOn`

English:
theorem Hom.inductionOn
  statement: {motive : {X Y : F C} -> (X ⟶ Y) -> Prop} {X Y : F C} (t : X ⟶ Y)
  proof: by
  induction t using Quotient.inductionOn with | _ f
  induction f with
  | id X => exact id X
  | α_hom X Y Z => exact α_hom X Y Z
  | α_inv X Y Z => exact α_inv X Y Z
  | l_hom X => exact l_hom X
  | l_inv X => exact l_inv X
  | ρ_hom X => exact ρ_hom X
  | ρ_inv X => exact ρ_inv X
  | comp f g 

中文:
定理 态射.inductionOn
  结论: {motive : {X Y : F C} -> (X ⟶ Y) -> 命题} {X Y : F C} (t : X ⟶ Y)
  证明: by
  induction t using Quotient.inductionOn with | _ f
  induction f with
  | id X => exact id X
  | α_hom X Y Z => exact α_hom X Y Z
  | α_inv X Y Z => exact α_inv X Y Z
  | l_hom X => exact l_hom X
  | l_inv X => exact l_inv X
  | ρ_hom X => exact ρ_hom X
  | ρ_inv X => exact ρ_inv X
  | comp f g 

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, l_hom, l_inv, tensor, whiskerLeft, whiskerRight
-/
theorem Hom.inductionOn {motive : {X Y : F C} -> (X ⟶ Y) -> Prop} {X Y : F C} (t : X ⟶ Y)
    (id : (X : F C) -> motive (𝟙 X))
    (α_hom : (X Y Z : F C) -> motive (α_ X Y Z).hom)
    (α_inv : (X Y Z : F C) -> motive (α_ X Y Z).inv)
    (l_hom : (X : F C) -> motive (fun_ X).hom)
    (l_inv : (X : F C) -> motive (fun_ X).inv)
    (ρ_hom : (X : F C) -> motive (ρ_ X).hom)
    (ρ_inv : (X : F C) -> motive (ρ_ X).inv)
    (comp : {X Y Z : F C} -> (f : X ⟶ Y) -> (g : Y ⟶ Z) -> motive f -> motive g -> motive (f ≫ g))
    (whiskerLeft : (X : F C) -> {Y Z : F C} -> (f : Y ⟶ Z) -> motive f -> motive (X ◁ f))
    (whiskerRight : {X Y : F C} -> (f : X ⟶ Y) -> (Z : F C) -> motive f -> motive (f ▷ Z)) :
    motive t := by
  induction t using Quotient.inductionOn with | _ f
  induction f with
  | id X => exact id X
  | α_hom X Y Z => exact α_hom X Y Z
  | α_inv X Y Z => exact α_inv X Y Z
  | l_hom X => exact l_hom X
  | l_inv X => exact l_inv X
  | ρ_hom X => exact ρ_hom X
  | ρ_inv X => exact ρ_inv X
  | comp f g hf hg => exact comp _ _ hf hg
  | whiskerLeft X f hf => exact whiskerLeft X _ hf
  | whiskerRight f X hf => exact whiskerRight _ X hf
  | @tensor W X Y Z f g hf hg =>
      have : homMk f otimesₘ homMk g = homMk f ▷ X ≫ Y ◁ homMk g :=
        Quotient.sound (HomEquiv.tensorHom_def f g)
      change motive (homMk f otimesₘ homMk g)
      rw [this]
      exact comp _ _ (whiskerRight _ _ hf) (whiskerLeft _ _ hg)

section Functor

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (f : C -> D)

/--
Definition of `projectObj` / `projectObj` 的定义

English:
definition projectObj
  signature: : F C -> D

中文:
定义 projectObj
  签名: : F C -> D
-/
def projectObj : F C -> D
  | FreeMonoidalCategory.of X => f X
  | FreeMonoidalCategory.unit => 𝟙_ D
  | FreeMonoidalCategory.tensor X Y => projectObj X otimes projectObj Y

section


open Hom

/-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
@[simp]
/--
Definition of `projectMapAux` / `projectMapAux` 的定义

English:
definition projectMapAux
  signature: : forall {X Y : F C}, (X ⟶ᵐ Y) -> (projectObj f X ⟶ projectObj f Y)

中文:
定义 projectMapAux
  签名: : 对任意 {X Y : F C}, (X ⟶ᵐ Y) -> (projectObj f X ⟶ projectObj f Y)
-/
def projectMapAux : forall {X Y : F C}, (X ⟶ᵐ Y) -> (projectObj f X ⟶ projectObj f Y)
  | _, _, Hom.id _ => 𝟙 _
  | _, _, α_hom _ _ _ => (α_ _ _ _).hom
  | _, _, α_inv _ _ _ => (α_ _ _ _).inv
  | _, _, l_hom _ => (fun_ _).hom
  | _, _, l_inv _ => (fun_ _).inv
  | _, _, ρ_hom _ => (ρ_ _).hom
  | _, _, ρ_inv _ => (ρ_ _).inv
  | _, _, Hom.comp f g => projectMapAux f ≫ projectMapAux g
  | _, _, Hom.whiskerLeft X p => projectObj f X ◁ projectMapAux p
  | _, _, Hom.whiskerRight p X => projectMapAux p ▷ projectObj f X
  | _, _, Hom.tensor f g => projectMapAux f otimesₘ projectMapAux g

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `FreeMonoidalCategory.project`. -/
@[simp]
/--
Definition of `projectMap` / `projectMap` 的定义

English:
definition projectMap
  signature: (X Y : F C)
  body: Quotient.lift (projectMapAux f) by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux,

中文:
定义 projectMap
  签名: (X Y : F C)
  定义体: Quotient.lift (projectMapAux f) by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux,

Depends on / 依赖: Quotient, Quotient.lift, hfg.trans, projectMapAux, projectObj, tensor, tensorHom_def, whiskerLeft, whiskerRight
-/
def projectMap (X Y : F C) : (X ⟶ Y) -> (projectObj f X ⟶ projectObj f Y) :=
Quotient.lift (projectMapAux f) by
    intro f g h
    induction h with
    | refl => rfl
    | symm _ _ _ hfg' => exact hfg'.symm
    | trans _ _ hfg hgh => exact hfg.trans hgh
    | comp _ _ hf hg => dsimp only [projectMapAux]; rw [hf, hg]
    | whiskerLeft _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | whiskerRight _ _ _ _ hf => dsimp only [projectMapAux, projectObj]; rw [hf]
    | tensor _ _ hfg hfg' => dsimp only [projectMapAux]; rw [hfg, hfg']
    | tensorHom_def _ _ =>
        dsimp only [projectMapAux, projectObj]; rw [MonoidalCategory.tensorHom_def]
    | comp_id => dsimp only [projectMapAux]; rw [Category.comp_id]
    | id_comp => dsimp only [projectMapAux]; rw [Category.id_comp]
    | assoc => dsimp only [projectMapAux]; rw [Category.assoc]
    | id_tensorHom_id => dsimp only [projectMapAux]; rw [MonoidalCategory.id_tensorHom_id]; rfl
    | tensorHom_comp_tensorHom =>
      dsimp only [projectMapAux]; rw [MonoidalCategory.tensorHom_comp_tensorHom]
    | whiskerLeft_id =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.whiskerLeft_id]
    | id_whiskerRight =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.id_whiskerRight]
    | α_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | α_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | associator_naturality =>
        dsimp only [projectMapAux]; rw [MonoidalCategory.associator_naturality]
    | ρ_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | ρ_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | ρ_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.rightUnitor_naturality]
    | l_hom_inv => dsimp only [projectMapAux]; rw [Iso.hom_inv_id]
    | l_inv_hom => dsimp only [projectMapAux]; rw [Iso.inv_hom_id]
    | l_naturality =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.leftUnitor_naturality]
    | pentagon =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.pentagon]
    | triangle =>
        dsimp only [projectMapAux, projectObj]
        rw [MonoidalCategory.triangle]

end

/--
Definition of `project` / `project` 的定义

English:
definition project
  signature: : F C ⥤ D where
  body: projectObj f
  map := projectMap f _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

中文:
定义 project
  签名: : F C ⥤ D where
  定义体: projectObj f
  map := projectMap f _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

Depends on / 依赖: projectObj
-/
def project : F C ⥤ D where
  obj := projectObj f
  map := projectMap f _ _
  map_comp := by rintro _ _ _ ⟨_⟩ ⟨_⟩; rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (project f).Monoidal
  body: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
  -- Porting note: `μIso_hom_natural_left` was proved in mathlib3 by tidy, using induction.
  -- We probably don't expect `cat_disch` to handle this yet, see https://leanprover.zulipchat.com/#narrow/stream/2

中文:
实例 :
  签名: (project f).幺半群
  定义体: Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
  -- Porting note: `μIso_hom_natural_left` was proved in mathlib3 by tidy, using induction.
  -- We probably don't expect `cat_disch` to handle this yet, see https://leanprover.zulipchat.com/#narrow/stream/2

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toMonoidal, Iso.refl, toMonoidal
-/
instance : (project f).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ => Iso.refl _
  -- Porting note: `μIso_hom_natural_left` was proved in mathlib3 by tidy, using induction.
  -- We probably don't expect `cat_disch` to handle this yet, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
      μIso_hom_natural_left := fun f _ => by
        induction f using Quotient.recOn
        all_goals aesop
      μIso_hom_natural_right := fun _ f => by
        induction f using Quotient.recOn
        all_goals aesop }

end Functor

end

end FreeMonoidalCategory

end CategoryTheory
