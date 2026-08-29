/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# The category of bimonoids in a braided monoidal category.

We define bimonoids in a braided monoidal category `C`
as comonoid objects in the category of monoid objects in `C`.

We verify that this is equivalent to the monoid objects in the category of comonoid objects.

## TODO
* Construct the category of modules, and show that it is monoidal with a monoidal forgetful functor
  to `C`.
* Some form of Tannaka reconstruction:
  given a monoidal functor `F : C ⥤ D` into a braided category `D`,
  the internal endomorphisms of `F` form a bimonoid in presheaves on `D`,
  in good circumstances this is representable by a bimonoid in `D`, and then
  `C` is monoidally equivalent to the modules over that bimonoid.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory C]

open scoped MonObj ComonObj

/--
Definition of `BimonObj` / `BimonObj` 的定义

English:
class BimonObj
  parameters: (M : C)
  extends: MonObj M, ComonObj M
  axioms and operations (4):
    - mul_comul((M)) : μ[M] ≫ Δ[M] = (Δ[M] otimesₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] otimesₘ μ[M])  [default: by cat_disch]
    - one_comul((M)) : η[M] ≫ Δ[M] = η[M otimes M]  [default: by cat_disch]
    - mul_counit((M)) : μ[M] ≫ ε[M] = ε[M otimes M]  [default: by cat_disch]
    - one_counit((M)) : η[M] ≫ ε[M] = 𝟙 (𝟙_ C)  [default: by cat_disch]

中文:
类 BimonObj
  参数: (M : C)
  继承: MonObj M, ComonObj M
  公理与运算 (4 个):
    - mul_comul((M)) : μ[M] ≫ Δ[M] = (Δ[M] otimesₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] otimesₘ μ[M])  [默认: by cat_disch]
    - one_comul((M)) : η[M] ≫ Δ[M] = η[M otimes M]  [默认: by cat_disch]
    - mul_counit((M)) : μ[M] ≫ ε[M] = ε[M otimes M]  [默认: by cat_disch]
    - one_counit((M)) : η[M] ≫ ε[M] = 𝟙 (𝟙_ C)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, mul_counit, one_comul, one_counit, otimes
-/
class BimonObj (M : C) extends MonObj M, ComonObj M where
  mul_comul (M) : μ[M] ≫ Δ[M] = (Δ[M] otimesₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] otimesₘ μ[M]) := by cat_disch
  one_comul (M) : η[M] ≫ Δ[M] = η[M otimes M] := by cat_disch
  mul_counit (M) : μ[M] ≫ ε[M] = ε[M otimes M] := by cat_disch
  one_counit (M) : η[M] ≫ ε[M] = 𝟙 (𝟙_ C) := by cat_disch

namespace BimonObj

attribute [reassoc (attr := simp)] mul_comul one_comul mul_counit one_counit

end BimonObj

/--
Definition of `IsBimonHom` / `IsBimonHom` 的定义

English:
class IsBimonHom
  parameters: {M N : C} [BimonObj M] [BimonObj N] (f : M ⟶ N)
  (no additional axioms)

中文:
类 IsBimonHom
  参数: {M N : C} [BimonObj M] [BimonObj N] (f : M ⟶ N)
  (无附加公理)
-/
class IsBimonHom {M N : C} [BimonObj M] [BimonObj N] (f : M ⟶ N) : Prop extends
    IsMonHom f, IsComonHom f

variable (C) in
/--
Definition of `Bimon` / `Bimon` 的定义

English:
definition Bimon
  body: Comon (Mon C)

中文:
定义 Bimon
  定义体: Comon (Mon C)
-/
def Bimon := Comon (Mon C)

namespace Bimon

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Bimon C)
  body: inferInstanceAs (Category (Comon (Mon C)))

中文:
实例 :
  签名: Category (Bimon C)
  定义体: inferInstanceAs (Category (Comon (Mon C)))

Depends on / 依赖: Category
-/
instance : Category (Bimon C) := inferInstanceAs (Category (Comon (Mon C)))

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom)
  statement: f = g
  proof: Comon.Hom.ext (Mon.Hom.ext w)

中文:
引理 ext
  条件: {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom)
  结论: f = g
  证明: Comon.Hom.ext (Mon.Hom.ext w)
-/
@[ext] lemma ext {X Y : Bimon C} {f g : X ⟶ Y} (w : f.hom.hom = g.hom.hom) : f = g :=
  Comon.Hom.ext (Mon.Hom.ext w)

/--
theorem `id_hom'` / 定理 `id_hom'`

English:
theorem id_hom'
  given: (M : Bimon C)
  statement: Comon.Hom.hom (𝟙 M) = 𝟙 M.X
  proof: rfl

@[simp]

中文:
定理 id_hom'
  条件: (M : Bimon C)
  结论: Comon.Hom.hom (𝟙 M) = 𝟙 M.X
  证明: rfl

@[simp]
-/
@[simp] theorem id_hom' (M : Bimon C) : Comon.Hom.hom (𝟙 M) = 𝟙 M.X := rfl

@[simp]
/--
theorem `comp_hom'` / 定理 `comp_hom'`

English:
theorem comp_hom'
  given: {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K)
  statement: (f ≫ g).hom = f.hom ≫ g.hom
  proof: rfl

中文:
定理 comp_hom'
  条件: {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K)
  结论: (f ≫ g).hom = f.hom ≫ g.hom
  证明: rfl
-/
theorem comp_hom' {M N K : Bimon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

variable (C)

/--
Definition of `toMon` / `toMon` 的定义

English:
abbreviation toMon
  signature: : Bimon C ⥤ Mon C
  body: Comon.forget (Mon C)

中文:
缩写 toMon
  签名: : Bimon C ⥤ Mon C
  定义体: Comon.forget (Mon C)

Depends on / 依赖: Comon.forget, forget
-/
abbrev toMon : Bimon C ⥤ Mon C := Comon.forget (Mon C)

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : Bimon C ⥤ C
  body: toMon C ⋙ Mon.forget C

@[simp]

中文:
定义 forget
  签名: : Bimon C ⥤ C
  定义体: toMon C ⋙ Mon.forget C

@[simp]

Depends on / 依赖: Mon.forget, forget
-/
def forget : Bimon C ⥤ C := toMon C ⋙ Mon.forget C

@[simp]
/--
theorem `toMon_forget` / 定理 `toMon_forget`

English:
theorem toMon_forget
  statement: toMon C ⋙ Mon.forget C = forget C
  proof: rfl

中文:
定理 toMon_forget
  结论: toMon C ⋙ Mon.forget C = forget C
  证明: rfl
-/
theorem toMon_forget : toMon C ⋙ Mon.forget C = forget C := rfl

/-- The forgetful functor from bimonoid objects to comonoid objects. -/
@[simps!]
/--
Definition of `toComon` / `toComon` 的定义

English:
definition toComon
  signature: : Bimon C ⥤ Comon C
  body: (Mon.forget C).mapComon

@[simp]

中文:
定义 toComon
  签名: : Bimon C ⥤ Comon C
  定义体: (Mon.forget C).mapComon

@[simp]

Depends on / 依赖: Mon.forget, WEqualsLocallyBijective, WEqualsLocallyBijective.mk, forget, mapComon
-/
def toComon : Bimon C ⥤ Comon C := (Mon.forget C).mapComon

@[simp]
/--
theorem `toComon_forget` / 定理 `toComon_forget`

English:
theorem toComon_forget
  statement: toComon C ⋙ Comon.forget C = forget C
  proof: rfl

中文:
定理 toComon_forget
  结论: toComon C ⋙ Comon.forget C = forget C
  证明: rfl
-/
theorem toComon_forget : toComon C ⋙ Comon.forget C = forget C := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The object level part of the forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/--
Definition of `toMonComonObj` / `toMonComonObj` 的定义

English:
definition toMonComonObj
  signature: (M : Bimon C)
  body: (toComon C).obj M
  mon.one := .mk' η[M.X.X]
  mon.mul.hom := μ[M.X.X]
  mon.mul.isComonHom_hom.hom_comul := by simp

中文:
定义 toMonComonObj
  签名: (M : Bimon C)
  定义体: (toComon C).obj M
  mon.one := .mk' η[M.X.X]
  mon.mul.hom := μ[M.X.X]
  mon.mul.isComonHom_hom.hom_comul := by simp

Depends on / 依赖: toComon
-/
def toMonComonObj (M : Bimon C) : Mon (Comon C) where
  X := (toComon C).obj M
  mon.one := .mk' η[M.X.X]
  mon.mul.hom := μ[M.X.X]
  mon.mul.isComonHom_hom.hom_comul := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/--
Definition of `toMonComon` / `toMonComon` 的定义

English:
definition toMonComon
  signature: : Bimon C ⥤ Mon (Comon C) where
  body: toMonComonObj
  map f := .mk' ((toComon C).map f)

中文:
定义 toMonComon
  签名: : Bimon C ⥤ Mon (Comon C) where
  定义体: toMonComonObj
  map f := .mk' ((toComon C).map f)

Depends on / 依赖: toMonComonObj
-/
def toMonComon : Bimon C ⥤ Mon (Comon C) where
  obj := toMonComonObj
  map f := .mk' ((toComon C).map f)

variable {C}

/-- Auxiliary definition for `ofMonComonObj`. -/
@[simps! X]
/--
Definition of `ofMonComonObjX` / `ofMonComonObjX` 的定义

English:
definition ofMonComonObjX
  signature: (M : Mon (Comon C))
  body: (Comon.forget C).mapMon.obj M

@[simp]

中文:
定义 ofMonComonObjX
  签名: (M : Mon (Comon C))
  定义体: (Comon.forget C).mapMon.obj M

@[simp]

Depends on / 依赖: Comon.forget, forget, mapMon, mapMon.obj
-/
def ofMonComonObjX (M : Mon (Comon C)) : Mon C := (Comon.forget C).mapMon.obj M

@[simp]
/--
theorem `ofMonComonObjX_one` / 定理 `ofMonComonObjX_one`

English:
theorem ofMonComonObjX_one
  given: (M : Mon (Comon C))
  proof: rfl

@[simp]

中文:
定理 ofMonComonObjX_one
  条件: (M : Mon (Comon C))
  证明: rfl

@[simp]
-/
theorem ofMonComonObjX_one (M : Mon (Comon C)) :
    η[(ofMonComonObjX M).X] = 𝟙 (𝟙_ C) ≫ η[M.X].hom :=
  rfl

@[simp]
/--
theorem `ofMonComonObjX_mul` / 定理 `ofMonComonObjX_mul`

English:
theorem ofMonComonObjX_mul
  given: (M : Mon (Comon C))
  proof: rfl

中文:
定理 ofMonComonObjX_mul
  条件: (M : Mon (Comon C))
  证明: rfl
-/
theorem ofMonComonObjX_mul (M : Mon (Comon C)) :
    μ[(ofMonComonObjX M).X] = 𝟙 (M.X.X otimes M.X.X) ≫ μ[M.X].hom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] ComonObj.instTensorUnit in
attribute [local simp] MonObj.tensorObj.one_def MonObj.tensorObj.mul_def tensorμ in
/-- The object level part of the backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/--
Definition of `ofMonComonObj` / `ofMonComonObj` 的定义

English:
definition ofMonComonObj
  signature: (M : Mon (Comon C))
  body: ofMonComonObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

中文:
定义 ofMonComonObj
  签名: (M : Mon (Comon C))
  定义体: ofMonComonObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

Depends on / 依赖: ofMonComonObjX
-/
def ofMonComonObj (M : Mon (Comon C)) : Bimon C where
  X := ofMonComonObjX M
  comon.counit := .mk' ε[M.X.X]
  comon.comul := .mk' Δ[M.X.X]

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- The backward direction of `Comon (Mon C) ≌ Mon (Comon C)` -/
@[simps]
/--
Definition of `ofMonComon` / `ofMonComon` 的定义

English:
definition ofMonComon
  signature: : Mon (Comon C) ⥤ Bimon C where
  body: ofMonComonObj
  map f := .mk' ((Comon.forget C).mapMon.map f)

中文:
定义 ofMonComon
  签名: : Mon (Comon C) ⥤ Bimon C where
  定义体: ofMonComonObj
  map f := .mk' ((Comon.forget C).mapMon.map f)

Depends on / 依赖: ofMonComonObj
-/
def ofMonComon : Mon (Comon C) ⥤ Bimon C where
  obj := ofMonComonObj
  map f := .mk' ((Comon.forget C).mapMon.map f)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toMonComon_ofMonComon_obj_one` / 定理 `toMonComon_ofMonComon_obj_one`

English:
theorem toMonComon_ofMonComon_obj_one
  given: (M : Bimon C)
  proof: rfl

中文:
定理 toMonComon_ofMonComon_obj_one
  条件: (M : Bimon C)
  证明: rfl
-/
theorem toMonComon_ofMonComon_obj_one (M : Bimon C) :
    η[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ η[M.X.X] :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `toMonComon_ofMonComon_obj_mul` / 定理 `toMonComon_ofMonComon_obj_mul`

English:
theorem toMonComon_ofMonComon_obj_mul
  given: (M : Bimon C)
  proof: rfl

中文:
定理 toMonComon_ofMonComon_obj_mul
  条件: (M : Bimon C)
  证明: rfl
-/
theorem toMonComon_ofMonComon_obj_mul (M : Bimon C) :
    μ[((toMonComon C ⋙ ofMonComon C).obj M).X.X] = 𝟙 _ ≫ μ[M.X.X] :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
/--
Definition of `equivMonComonUnitIsoAppXAux` / `equivMonComonUnitIsoAppXAux` 的定义

English:
definition equivMonComonUnitIsoAppXAux
  signature: (M : Bimon C)
  body: Iso.refl _

中文:
定义 equivMonComonUnitIsoAppXAux
  签名: (M : Bimon C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def equivMonComonUnitIsoAppXAux (M : Bimon C) :
    M.X.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X.X :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
instance (M : Bimon C) : IsMonHom (equivMonComonUnitIsoAppXAux M).hom where

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `equivMonComonUnitIsoApp`. -/
@[simps!]
/--
Definition of `equivMonComonUnitIsoAppX` / `equivMonComonUnitIsoAppX` 的定义

English:
definition equivMonComonUnitIsoAppX
  signature: (M : Bimon C)
  body: Mon.mkIso (equivMonComonUnitIsoAppXAux M)

中文:
定义 equivMonComonUnitIsoAppX
  签名: (M : Bimon C)
  定义体: Mon.mkIso (equivMonComonUnitIsoAppXAux M)

Depends on / 依赖: Mon.mkIso, equivMonComonUnitIsoAppXAux
-/
def equivMonComonUnitIsoAppX (M : Bimon C) :
    M.X ≅ ((toMonComon C ⋙ ofMonComon C).obj M).X :=
  Mon.mkIso (equivMonComonUnitIsoAppXAux M)

set_option backward.isDefEq.respectTransparency false in
instance (M : Bimon C) : IsComonHom (equivMonComonUnitIsoAppX M).hom where

/-- The unit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
/--
Definition of `equivMonComonUnitIsoApp` / `equivMonComonUnitIsoApp` 的定义

English:
definition equivMonComonUnitIsoApp
  signature: (M : Bimon C)
  body: Comon.mkIso' (equivMonComonUnitIsoAppX M)

@[simp]

中文:
定义 equivMonComonUnitIsoApp
  签名: (M : Bimon C)
  定义体: Comon.mkIso' (equivMonComonUnitIsoAppX M)

@[simp]

Depends on / 依赖: Comon.mkIso, equivMonComonUnitIsoAppX
-/
def equivMonComonUnitIsoApp (M : Bimon C) :
    M ≅ (toMonComon C ⋙ ofMonComon C).obj M :=
  Comon.mkIso' (equivMonComonUnitIsoAppX M)

@[simp]
/--
theorem `ofMonComon_toMonComon_obj_counit` / 定理 `ofMonComon_toMonComon_obj_counit`

English:
theorem ofMonComon_toMonComon_obj_counit
  given: (M : Mon (Comon C))
  proof: rfl

@[simp]

中文:
定理 ofMonComon_toMonComon_obj_counit
  条件: (M : Mon (Comon C))
  证明: rfl

@[simp]

Depends on / 依赖: G.Full, G.IsLocallyFull, IsLocallyFull, IsLocallyFull.of_full, of_full
-/
theorem ofMonComon_toMonComon_obj_counit (M : Mon (Comon C)) :
    ε[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = ε[M.X.X] ≫ 𝟙 _ :=
  rfl

@[simp]
/--
theorem `ofMonComon_toMonComon_obj_comul` / 定理 `ofMonComon_toMonComon_obj_comul`

English:
theorem ofMonComon_toMonComon_obj_comul
  given: (M : Mon (Comon C))
  proof: rfl

#adaptation_note

中文:
定理 ofMonComon_toMonComon_obj_comul
  条件: (M : Mon (Comon C))
  证明: rfl

#adaptation_note

Depends on / 依赖: Faithful, G.Faithful, G.IsLocallyFaithful, IsLocallyFaithful, IsLocallyFaithful.of_faithful, of_faithful
-/
theorem ofMonComon_toMonComon_obj_comul (M : Mon (Comon C)) :
    Δ[((ofMonComon C ⋙ toMonComon C).obj M).X.X] = Δ[M.X.X] ≫ 𝟙 _ :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
/--
Definition of `equivMonComonCounitIsoAppXAux` / `equivMonComonCounitIsoAppXAux` 的定义

English:
definition equivMonComonCounitIsoAppXAux
  signature: (M : Mon (Comon C))
  body: Iso.refl _

中文:
定义 equivMonComonCounitIsoAppXAux
  签名: (M : Mon (Comon C))
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def equivMonComonCounitIsoAppXAux (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X.X ≅ M.X.X :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
instance (M : Mon (Comon C)) : IsComonHom (equivMonComonCounitIsoAppXAux M).hom where

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `equivMonComonCounitIsoApp`. -/
@[simps!]
/--
Definition of `equivMonComonCounitIsoAppX` / `equivMonComonCounitIsoAppX` 的定义

English:
definition equivMonComonCounitIsoAppX
  signature: (M : Mon (Comon C))
  body: Comon.mkIso' (equivMonComonCounitIsoAppXAux M)

中文:
定义 equivMonComonCounitIsoAppX
  签名: (M : Mon (Comon C))
  定义体: Comon.mkIso' (equivMonComonCounitIsoAppXAux M)

Depends on / 依赖: Comon.mkIso, equivMonComonCounitIsoAppXAux
-/
def equivMonComonCounitIsoAppX (M : Mon (Comon C)) :
    ((ofMonComon C ⋙ toMonComon C).obj M).X ≅ M.X :=
  Comon.mkIso' (equivMonComonCounitIsoAppXAux M)

set_option backward.isDefEq.respectTransparency false in
instance (M : Mon (Comon C)) : IsMonHom (equivMonComonCounitIsoAppX M).hom where

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the equivalence `Comon (Mon C) ≌ Mon (Comon C)`. -/
@[simps!]
/--
Definition of `equivMonComonCounitIsoApp` / `equivMonComonCounitIsoApp` 的定义

English:
definition equivMonComonCounitIsoApp
  signature: (M : Mon (Comon C))
  body: Mon.mkIso (equivMonComonCounitIsoAppX M)

中文:
定义 equivMonComonCounitIsoApp
  签名: (M : Mon (Comon C))
  定义体: Mon.mkIso (equivMonComonCounitIsoAppX M)

Depends on / 依赖: Mon.mkIso, equivMonComonCounitIsoAppX
-/
def equivMonComonCounitIsoApp (M : Mon (Comon C)) :
    (ofMonComon C ⋙ toMonComon C).obj M ≅ M :=
Mon.mkIso (equivMonComonCounitIsoAppX M)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `equivMonComon` / `equivMonComon` 的定义

English:
definition equivMonComon
  signature: : Bimon C ≌ Mon (Comon C) where
  body: toMonComon C
  inverse := ofMonComon C
  unitIso := NatIso.ofComponents equivMonComonUnitIsoApp
  counitIso := NatIso.ofComponents equivMonComonCounitIsoApp

中文:
定义 equivMonComon
  签名: : Bimon C ≌ Mon (Comon C) where
  定义体: toMonComon C
  inverse := ofMonComon C
  unitIso := NatIso.ofComponents equivMonComonUnitIsoApp
  counitIso := NatIso.ofComponents equivMonComonCounitIsoApp

Depends on / 依赖: toMonComon
-/
def equivMonComon : Bimon C ≌ Mon (Comon C) where
  functor := toMonComon C
  inverse := ofMonComon C
  unitIso := NatIso.ofComponents equivMonComonUnitIsoApp
  counitIso := NatIso.ofComponents equivMonComonCounitIsoApp

/-! ### The trivial bimonoid -/

variable (C) in
/-- The trivial bimonoid object. -/
@[simps!]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : Bimon C
  body: Comon.trivial (Mon C)

中文:
定义 trivial
  签名: : Bimon C
  定义体: Comon.trivial (Mon C)

Depends on / 依赖: Comon.trivial
-/
def trivial : Bimon C := Comon.trivial (Mon C)

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimonoid morphism from the trivial bimonoid to any bimonoid. -/
@[simps]
/--
Definition of `trivialTo` / `trivialTo` 的定义

English:
definition trivialTo
  signature: (A : Bimon C)
  body: .mk' (default : Mon.trivial C ⟶ A.X)

中文:
定义 trivialTo
  签名: (A : Bimon C)
  定义体: .mk' (default : Mon.trivial C ⟶ A.X)

Depends on / 依赖: Mon.trivial
-/
def trivialTo (A : Bimon C) : trivial C ⟶ A :=
  .mk' (default : Mon.trivial C ⟶ A.X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimonoid morphism from any bimonoid to the trivial bimonoid. -/
@[simps!]
/--
Definition of `toTrivial` / `toTrivial` 的定义

English:
definition toTrivial
  signature: (A : Bimon C)
  body: (default : @Quiver.Hom (Comon (Mon C)) _ A (Comon.trivial (Mon C)))

中文:
定义 toTrivial
  签名: (A : Bimon C)
  定义体: (default : @Quiver.Hom (Comon (Mon C)) _ A (Comon.trivial (Mon C)))

Depends on / 依赖: Comon.trivial, Quiver, Quiver.Hom
-/
def toTrivial (A : Bimon C) : A ⟶ trivial C :=
  (default : @Quiver.Hom (Comon (Mon C)) _ A (Comon.trivial (Mon C)))

/-! ### Additional lemmas -/

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `BimonObjAux_counit` / 定理 `BimonObjAux_counit`

English:
theorem BimonObjAux_counit
  given: (M : Bimon C)
  proof: Category.comp_id _

中文:
定理 BimonObjAux_counit
  条件: (M : Bimon C)
  证明: Category.comp_id _

Depends on / 依赖: Category, Category.comp_id, comp_id
-/
theorem BimonObjAux_counit (M : Bimon C) :
    ε[((toComon C).obj M).X] = ε[M.X].hom :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `BimonObjAux_comul` / 定理 `BimonObjAux_comul`

English:
theorem BimonObjAux_comul
  given: (M : Bimon C)
  proof: Category.comp_id _

中文:
定理 BimonObjAux_comul
  条件: (M : Bimon C)
  证明: Category.comp_id _

Depends on / 依赖: Category, Category.comp_id, comp_id
-/
theorem BimonObjAux_comul (M : Bimon C) :
    Δ[((toComon C).obj M).X] = Δ[M.X].hom :=
  Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
instance (M : Bimon C) : BimonObj M.X.X where
  counit := ε[M.X].hom
  comul := Δ[M.X].hom
  counit_comul := by
    rw [← BimonObjAux_counit]; rw [← BimonObjAux_comul]; rw [ComonObj.counit_comul]
  comul_counit := by
    rw [← BimonObjAux_counit]; rw [← BimonObjAux_comul]; rw [ComonObj.comul_counit]
  comul_assoc := by
    simp_rw [← BimonObjAux_comul, ComonObj.comul_assoc]

attribute [local simp] MonObj.tensorObj.one_def in
@[reassoc]
/--
theorem `one_comul` / 定理 `one_comul`

English:
theorem one_comul
  given: (M : C) [BimonObj M]
  proof: by
  simp

@[reassoc]

中文:
定理 one_comul
  条件: (M : C) [BimonObj M]
  证明: by
  simp

@[reassoc]
-/
theorem one_comul (M : C) [BimonObj M] :
    η[M] ≫ Δ[M] = (fun_ _).inv ≫ (η[M] otimesₘ η[M]) := by
  simp

@[reassoc]
/--
theorem `mul_counit` / 定理 `mul_counit`

English:
theorem mul_counit
  given: (M : C) [BimonObj M]
  proof: by
  simp

中文:
定理 mul_counit
  条件: (M : C) [BimonObj M]
  证明: by
  simp
-/
theorem mul_counit (M : C) [BimonObj M] :
    μ[M] ≫ ε[M] = (ε[M] otimesₘ ε[M]) ≫ (fun_ _).hom := by
  simp

/--
theorem `compatibility` / 定理 `compatibility`

English:
theorem compatibility
  given: (M : C) [BimonObj M]
  proof: by
  simp only [BimonObj.mul_comul, tensorμ, Category.assoc]

中文:
定理 compatibility
  条件: (M : C) [BimonObj M]
  证明: by
  simp only [BimonObj.mul_comul, tensorμ, Category.assoc]
-/
@[reassoc (attr := simp)] theorem compatibility (M : C) [BimonObj M] :
    (Δ[M] otimesₘ Δ[M]) ≫
      (α_ _ _ (M otimes M)).hom ≫ M ◁ (α_ _ _ _).inv ≫
      M ◁ (β_ M M).hom ▷ M ≫
      M ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫
      (μ[M] otimesₘ μ[M]) =
    μ[M] ≫ Δ[M] := by
  simp only [BimonObj.mul_comul, tensorμ, Category.assoc]

/-- Auxiliary definition for `Bimon.mk'`. -/
@[simps X]
/--
Definition of `mk'X` / `mk'X` 的定义

English:
definition mk'X
  signature: (X : C) [BimonObj X]
  body: { X := X }

中文:
定义 mk'X
  签名: (X : C) [BimonObj X]
  定义体: { X := X }
-/
def mk'X (X : C) [BimonObj X] : Mon C := { X := X }

set_option backward.isDefEq.respectTransparency false in
/-- Construct an object of `Bimon C` from an object `X : C` and `BimonObj X` instance. -/
@[simps X]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (X : C) [BimonObj X]
  body: mk'X X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X otimes X) }

中文:
定义 mk'
  签名: (X : C) [BimonObj X]
  定义体: mk'X X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X otimes X) }
-/
def mk' (X : C) [BimonObj X] : Bimon C where
  X := mk'X X
  comon :=
    { counit := .mk' (ε : X ⟶ 𝟙_ C)
      comul := .mk' (Δ : X ⟶ X otimes X) }

end Bimon
end CategoryTheory
