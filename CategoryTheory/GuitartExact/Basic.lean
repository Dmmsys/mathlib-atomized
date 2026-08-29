/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Guitart exact squares

Given four functors `T`, `L`, `R` and `B`, a 2-square `TwoSquare T L R B` consists of
a natural transformation `w : T ⋙ R ⟶ L ⋙ B`:
```
     T
  C₁ ⥤ C₂
L | | R
  v v
  C₃ ⥤ C₄
     B
```

In this file, we define a typeclass `w.GuitartExact` which expresses
that this square is exact in the sense of Guitart. This means that
for any `X₃ : C₃`, the induced functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)` is final.
It is also equivalent to the fact that for any `X₂ : C₂`, the
induced functor `StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`
is initial.

Various categorical notions (fully faithful functors, adjunctions, etc.) can
be characterized in terms of Guitart exact squares. Their particular role
in pointwise Kan extensions shall also be used in the construction of
derived functors.

## TODO

* Define the notion of derivability structure from
  [the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008] using Guitart exact squares
  and construct (pointwise) derived functors using this notion

## References
* https://ncatlab.org/nlab/show/exact+square
* [René Guitart, *Relations et carrés exacts*][Guitart1980]
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace TwoSquare

variable {T L R B} (w : TwoSquare T L R B)

/-- Given `w : TwoSquare T L R B` and `X₃ : C₃`, this is the obvious functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)`. -/
@[simps! obj map]
/--
Definition of `costructuredArrowRightwards` / `costructuredArrowRightwards` 的定义

English:
definition costructuredArrowRightwards
  signature: (X₃ : C₃)
  body: CostructuredArrow.post L B X₃ ⋙ Comma.mapLeft _ w ⋙
    CostructuredArrow.pre T R (B.obj X₃)

中文:
定义 costructuredArrowRightwards
  签名: (X₃ : C₃)
  定义体: CostructuredArrow.post L B X₃ ⋙ Comma.mapLeft _ w ⋙
    CostructuredArrow.pre T R (B.obj X₃)

Depends on / 依赖: B.obj, Comma.mapLeft, CostructuredArrow, CostructuredArrow.post, CostructuredArrow.pre, mapLeft
-/
def costructuredArrowRightwards (X₃ : C₃) :
    CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃) :=
  CostructuredArrow.post L B X₃ ⋙ Comma.mapLeft _ w ⋙
    CostructuredArrow.pre T R (B.obj X₃)

/-- Given `w : TwoSquare T L R B` and `X₂ : C₂`, this is the obvious functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`. -/
@[simps! obj map]
/--
Definition of `structuredArrowDownwards` / `structuredArrowDownwards` 的定义

English:
definition structuredArrowDownwards
  signature: (X₂ : C₂)
  body: StructuredArrow.post X₂ T R ⋙ Comma.mapRight _ w ⋙
    StructuredArrow.pre (R.obj X₂) L B

中文:
定义 structuredArrowDownwards
  签名: (X₂ : C₂)
  定义体: StructuredArrow.post X₂ T R ⋙ Comma.mapRight _ w ⋙
    StructuredArrow.pre (R.obj X₂) L B

Depends on / 依赖: Category, Category.assoc, Comma.mapRight, Discrete, Discrete.functor_obj, Fan.op, IsColimit, IsColimit.fac, IsLimit, IsLimit.fac, Iso.inv_comp_eq, Quiver, Quiver.Hom.op_inj, Quiver.Hom.op_unop, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, R.obj, StructuredArrow, StructuredArrow.post, StructuredArrow.pre
-/
def structuredArrowDownwards (X₂ : C₂) :
    StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B :=
  StructuredArrow.post X₂ T R ⋙ Comma.mapRight _ w ⋙
    StructuredArrow.pre (R.obj X₂) L B

section

variable {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)

/- In [the paper by Kahn and Maltsiniotis, §4.3][KahnMaltsiniotis2008], given
`w : TwoSquare T L R B` and `g : R.obj X₂ ⟶ B.obj X₃`, a category `J` is introduced
and it is observed that it is equivalent to the two categories
`w.StructuredArrowRightwards g` and `w.CostructuredArrowDownwards g`. We shall show below
that there is an equivalence
`w.equivalenceJ g : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`. -/

/--
Definition of `StructuredArrowRightwards` / `StructuredArrowRightwards` 的定义

English:
abbreviation StructuredArrowRightwards
  body: StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)

中文:
缩写 StructuredArrowRightwards
  定义体: StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, StructuredArrow, costructuredArrowRightwards, w.costructuredArrowRightwards
-/
abbrev StructuredArrowRightwards :=
  StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)

/--
Definition of `CostructuredArrowDownwards` / `CostructuredArrowDownwards` 的定义

English:
abbreviation CostructuredArrowDownwards
  body: CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)

中文:
缩写 CostructuredArrowDownwards
  定义体: CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)

Depends on / 依赖: CostructuredArrow, StructuredArrow, StructuredArrow.mk, structuredArrowDownwards, w.structuredArrowDownwards
-/
abbrev CostructuredArrowDownwards :=
  CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)

section

variable (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)

/--
Definition of `StructuredArrowRightwards.mk` / `StructuredArrowRightwards.mk` 的定义

English:
abbreviation StructuredArrowRightwards.mk
  signature: (comm : R.map a ≫ w.app X₁ ≫ B.map b = g)
  body: StructuredArrow.mk (Y := CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

中文:
缩写 StructuredArrowRightwards.mk
  签名: (comm : R.map a ≫ w.app X₁ ≫ B.map b = g)
  定义体: StructuredArrow.mk (Y := CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, StructuredArrow, StructuredArrow.mk
-/
abbrev StructuredArrowRightwards.mk (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
    w.StructuredArrowRightwards g :=
  StructuredArrow.mk (Y := CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `CostructuredArrowDownwards.mk` / `CostructuredArrowDownwards.mk` 的定义

English:
abbreviation CostructuredArrowDownwards.mk
  signature: (comm : R.map a ≫ w.app X₁ ≫ B.map b = g)
  body: CostructuredArrow.mk (Y := StructuredArrow.mk a)
    (StructuredArrow.homMk b (by simpa using comm))

中文:
缩写 CostructuredArrowDownwards.mk
  签名: (comm : R.map a ≫ w.app X₁ ≫ B.map b = g)
  定义体: CostructuredArrow.mk (Y := StructuredArrow.mk a)
    (StructuredArrow.homMk b (by simpa using comm))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk
-/
abbrev CostructuredArrowDownwards.mk (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
    w.CostructuredArrowDownwards g :=
  CostructuredArrow.mk (Y := StructuredArrow.mk a)
    (StructuredArrow.homMk b (by simpa using comm))

variable {w g}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `StructuredArrowRightwards.mk_surjective` / 引理 `StructuredArrowRightwards.mk_surjective`

English:
lemma StructuredArrowRightwards.mk_surjective
  proof: by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.mk_surjective f
  obtain ⟨X₁, b, rfl⟩ := g.mk_surjective
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

中文:
引理 StructuredArrowRightwards.mk_surjective
  证明: by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.mk_surjective f
  obtain ⟨X₁, b, rfl⟩ := g.mk_surjective
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk_surjective, StructuredArrow, StructuredArrow.mk_surjective, g.mk_surjective, homMk_surjective, mk_surjective
-/
lemma StructuredArrowRightwards.mk_surjective
    (f : w.StructuredArrowRightwards g) :
    exists (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)
      (comm : R.map a ≫ w.app X₁ ≫ B.map b = g), f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.mk_surjective f
  obtain ⟨X₁, b, rfl⟩ := g.mk_surjective
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `CostructuredArrowDownwards.mk_surjective` / 引理 `CostructuredArrowDownwards.mk_surjective`

English:
lemma CostructuredArrowDownwards.mk_surjective
  proof: by
  obtain ⟨g, φ, rfl⟩ := CostructuredArrow.mk_surjective f
  obtain ⟨X₁, a, rfl⟩ := g.mk_surjective
  obtain ⟨b, hb, rfl⟩ := StructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using hb, rfl⟩

中文:
引理 CostructuredArrowDownwards.mk_surjective
  证明: by
  obtain ⟨g, φ, rfl⟩ := CostructuredArrow.mk_surjective f
  obtain ⟨X₁, a, rfl⟩ := g.mk_surjective
  obtain ⟨b, hb, rfl⟩ := StructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using hb, rfl⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk_surjective, StructuredArrow, StructuredArrow.homMk_surjective, g.mk_surjective, homMk_surjective, mk_surjective
-/
lemma CostructuredArrowDownwards.mk_surjective
    (f : w.CostructuredArrowDownwards g) :
    exists (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)
      (comm : R.map a ≫ w.app X₁ ≫ B.map b = g), f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := CostructuredArrow.mk_surjective f
  obtain ⟨X₁, a, rfl⟩ := g.mk_surjective
  obtain ⟨b, hb, rfl⟩ := StructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using hb, rfl⟩

end

namespace EquivalenceJ

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g where
  body: CostructuredArrow.mk (Y := StructuredArrow.mk f.hom.left)
      (StructuredArrow.homMk f.right.hom (by simpa using CostructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    CostructuredArrow.homMk (StructuredArrow.homMk φ.right.left
      (by dsimp; rw [← StructuredArrow.w φ]; rfl))
      (by ext; exact Co

中文:
定义 functor
  签名: : w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g where
  定义体: CostructuredArrow.mk (Y := StructuredArrow.mk f.hom.left)
      (StructuredArrow.homMk f.right.hom (by simpa using CostructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    CostructuredArrow.homMk (StructuredArrow.homMk φ.right.left
      (by dsimp; rw [← StructuredArrow.w φ]; rfl))
      (by ext; exact Co

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, StructuredArrow, StructuredArrow.mk, f.hom.left
-/
def functor : w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g where
  obj f := CostructuredArrow.mk (Y := StructuredArrow.mk f.hom.left)
      (StructuredArrow.homMk f.right.hom (by simpa using CostructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    CostructuredArrow.homMk (StructuredArrow.homMk φ.right.left
      (by dsimp; rw [← StructuredArrow.w φ]; rfl))
      (by ext; exact CostructuredArrow.w φ.right)
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g where
  body: StructuredArrow.mk (Y := CostructuredArrow.mk f.hom.right)
      (CostructuredArrow.homMk f.left.hom (by simpa using StructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    StructuredArrow.homMk (CostructuredArrow.homMk φ.left.right
      (by dsimp; rw [← CostructuredArrow.w φ]; rfl))
      (by ext; exact 

中文:
定义 inverse
  签名: : w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g where
  定义体: StructuredArrow.mk (Y := CostructuredArrow.mk f.hom.right)
      (CostructuredArrow.homMk f.left.hom (by simpa using StructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    StructuredArrow.homMk (CostructuredArrow.homMk φ.left.right
      (by dsimp; rw [← CostructuredArrow.w φ]; rfl))
      (by ext; exact 

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, StructuredArrow, StructuredArrow.mk, f.hom.right
-/
def inverse : w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g where
  obj f := StructuredArrow.mk (Y := CostructuredArrow.mk f.hom.right)
      (CostructuredArrow.homMk f.left.hom (by simpa using StructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    StructuredArrow.homMk (CostructuredArrow.homMk φ.left.right
      (by dsimp; rw [← CostructuredArrow.w φ]; rfl))
      (by ext; exact StructuredArrow.w φ.left)
  map_id _ := rfl
  map_comp _ _ := rfl

end EquivalenceJ

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious equivalence of categories
`w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`. -/
@[simps functor inverse unitIso counitIso]
/--
Definition of `equivalenceJ` / `equivalenceJ` 的定义

English:
definition equivalenceJ
  signature: : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g where
  body: EquivalenceJ.functor w g
  inverse := EquivalenceJ.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 equivalenceJ
  签名: : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g where
  定义体: EquivalenceJ.functor w g
  inverse := EquivalenceJ.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: EquivalenceJ, EquivalenceJ.functor, functor
-/
def equivalenceJ : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g where
  functor := EquivalenceJ.functor w g
  inverse := EquivalenceJ.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
lemma `isConnected_rightwards_iff_downwards` / 引理 `isConnected_rightwards_iff_downwards`

English:
lemma isConnected_rightwards_iff_downwards
  proof: isConnected_iff_of_equivalence (w.equivalenceJ g)

中文:
引理 isConnected_rightwards_iff_downwards
  证明: isConnected_iff_of_equivalence (w.equivalenceJ g)

Depends on / 依赖: equivalenceJ, isConnected_iff_of_equivalence, w.equivalenceJ
-/
lemma isConnected_rightwards_iff_downwards :
    IsConnected (w.StructuredArrowRightwards g) ↔ IsConnected (w.CostructuredArrowDownwards g) :=
  isConnected_iff_of_equivalence (w.equivalenceJ g)

end

section

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g'` induced
by a morphism `γ` such that `R.map γ ≫ g = g'`. -/
@[simps]
/--
Definition of `costructuredArrowDownwardsPrecomp` / `costructuredArrowDownwardsPrecomp` 的定义

English:
definition costructuredArrowDownwardsPrecomp
  body: CostructuredArrowDownwards.mk _ _ A.left.right (γ ≫ A.left.hom) A.hom.right
    (by simpa [← hγ] using R.map γ ≫= StructuredArrow.w A.hom)
  map {A A'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right (by
      dsimp
      rw [assoc]; rw [StructuredArrow.w])) (by
    ext
    dsimp
  

中文:
定义 costructuredArrowDownwardsPrecomp
  定义体: CostructuredArrowDownwards.mk _ _ A.left.right (γ ≫ A.left.hom) A.hom.right
    (by simpa [← hγ] using R.map γ ≫= StructuredArrow.w A.hom)
  map {A A'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right (by
      dsimp
      rw [assoc]; rw [StructuredArrow.w])) (by
    ext
    dsimp
  

Depends on / 依赖: A.hom.right, A.left.hom, A.left.right, CostructuredArrowDownwards, CostructuredArrowDownwards.mk
-/
def costructuredArrowDownwardsPrecomp
    {X₂ X₂' : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) (g' : R.obj X₂' ⟶ B.obj X₃)
    (γ : X₂' ⟶ X₂) (hγ : R.map γ ≫ g = g') :
    w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g' where
  obj A := CostructuredArrowDownwards.mk _ _ A.left.right (γ ≫ A.left.hom) A.hom.right
    (by simpa [← hγ] using R.map γ ≫= StructuredArrow.w A.hom)
  map {A A'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right (by
      dsimp
      rw [assoc]; rw [StructuredArrow.w])) (by
    ext
    dsimp
    rw [← CostructuredArrow.w φ]; rw [structuredArrowDownwards_map]
    rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

end

/--
Definition of `GuitartExact` / `GuitartExact` 的定义

English:
class GuitartExact
  parameters: : Prop where
  axioms and operations (1):
    - isConnected_rightwards({X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)) : IsConnected (w.StructuredArrowRightwards g)

中文:
类 GuitartExact
  参数: : 命题 where
  公理与运算 (1 个):
    - isConnected_rightwards({X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)) : 是连通 (w.StructuredArrowRightwards g)
-/
class GuitartExact : Prop where
  isConnected_rightwards {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) :
    IsConnected (w.StructuredArrowRightwards g)

/--
lemma `guitartExact_iff_isConnected_rightwards` / 引理 `guitartExact_iff_isConnected_rightwards`

English:
lemma guitartExact_iff_isConnected_rightwards
  proof: ⟨fun h => h.isConnected_rightwards, fun h => ⟨h⟩⟩

中文:
引理 guitartExact_iff_isConnected_rightwards
  证明: ⟨fun h => h.isConnected_rightwards, fun h => ⟨h⟩⟩

Depends on / 依赖: h.isConnected_rightwards, isConnected_rightwards
-/
lemma guitartExact_iff_isConnected_rightwards :
    w.GuitartExact ↔ forall {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (w.StructuredArrowRightwards g) :=
  ⟨fun h => h.isConnected_rightwards, fun h => ⟨h⟩⟩

/--
lemma `guitartExact_iff_isConnected_downwards` / 引理 `guitartExact_iff_isConnected_downwards`

English:
lemma guitartExact_iff_isConnected_downwards
  proof: by
  simp only [guitartExact_iff_isConnected_rightwards,
    isConnected_rightwards_iff_downwards]

中文:
引理 guitartExact_iff_isConnected_downwards
  证明: by
  simp only [guitartExact_iff_isConnected_rightwards,
    isConnected_rightwards_iff_downwards]

Depends on / 依赖: guitartExact_iff_isConnected_rightwards, isConnected_rightwards_iff_downwards
-/
lemma guitartExact_iff_isConnected_downwards :
    w.GuitartExact ↔ forall {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (w.CostructuredArrowDownwards g) := by
  simp only [guitartExact_iff_isConnected_rightwards,
    isConnected_rightwards_iff_downwards]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hw
  signature: : w.GuitartExact] {X₃ : C₃} (g : CostructuredArrow R (B.obj X₃)) :
  body: by
  rw [guitartExact_iff_isConnected_rightwards] at hw
  apply hw

中文:
实例 [hw
  签名: : w.GuitartExact] {X₃ : C₃} (g : CostructuredArrow R (B.obj X₃)) :
  定义体: by
  rw [guitartExact_iff_isConnected_rightwards] at hw
  apply hw

Depends on / 依赖: guitartExact_iff_isConnected_rightwards
-/
instance [hw : w.GuitartExact] {X₃ : C₃} (g : CostructuredArrow R (B.obj X₃)) :
    IsConnected (StructuredArrow g (w.costructuredArrowRightwards X₃)) := by
  rw [guitartExact_iff_isConnected_rightwards] at hw
  apply hw

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hw
  signature: : w.GuitartExact] {X₂ : C₂} (g : StructuredArrow (R.obj X₂) B) :
  body: by
  rw [guitartExact_iff_isConnected_downwards] at hw
  apply hw

中文:
实例 [hw
  签名: : w.GuitartExact] {X₂ : C₂} (g : 结构化箭头 (R.obj X₂) B) :
  定义体: by
  rw [guitartExact_iff_isConnected_downwards] at hw
  apply hw

Depends on / 依赖: guitartExact_iff_isConnected_downwards
-/
instance [hw : w.GuitartExact] {X₂ : C₂} (g : StructuredArrow (R.obj X₂) B) :
    IsConnected (CostructuredArrow (w.structuredArrowDownwards X₂) g) := by
  rw [guitartExact_iff_isConnected_downwards] at hw
  apply hw

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `costructuredArrowRightwards_final_iff_of_iso` / 引理 `costructuredArrowRightwards_final_iff_of_iso`

English:
lemma costructuredArrowRightwards_final_iff_of_iso
  given: {X₃ X₃' : C₃} (e : X₃ ≅ X₃')
  proof: by
  rw [Functor.final_iff_comp_equivalence _ (CostructuredArrow.mapIso (B.mapIso e)).functor]; rw [Functor.final_iff_equivalence_comp (CostructuredArrow.mapIso e).functor]
  exact Functor.final_natIso_iff
    (NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _)))

中文:
引理 costructuredArrowRightwards_final_iff_of_iso
  条件: {X₃ X₃' : C₃} (e : X₃ ≅ X₃')
  证明: by
  rw [Functor.final_iff_comp_equivalence _ (CostructuredArrow.mapIso (B.mapIso e)).functor]; rw [Functor.final_iff_equivalence_comp (CostructuredArrow.mapIso e).functor]
  exact Functor.final_natIso_iff
    (NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _)))

Depends on / 依赖: B.mapIso, CostructuredArrow, CostructuredArrow.isoMk, CostructuredArrow.mapIso, Functor, Functor.final_iff_comp_equivalence, Functor.final_iff_equivalence_comp, Functor.final_natIso_iff, Iso.refl, NatIso, NatIso.ofComponents, final_iff_comp_equivalence, final_iff_equivalence_comp, final_natIso_iff, functor, mapIso, ofComponents
-/
lemma costructuredArrowRightwards_final_iff_of_iso {X₃ X₃' : C₃} (e : X₃ ≅ X₃') :
    (w.costructuredArrowRightwards X₃).Final ↔
      (w.costructuredArrowRightwards X₃').Final := by
  rw [Functor.final_iff_comp_equivalence _ (CostructuredArrow.mapIso (B.mapIso e)).functor]; rw [Functor.final_iff_equivalence_comp (CostructuredArrow.mapIso e).functor]
  exact Functor.final_natIso_iff
    (NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _)))

/--
lemma `guitartExact_iff_final` / 引理 `guitartExact_iff_final`

English:
lemma guitartExact_iff_final
  proof: ⟨fun _ _ => ⟨fun _ => inferInstance⟩, fun _ => ⟨fun _ => inferInstance⟩⟩

中文:
引理 guitartExact_iff_final
  证明: ⟨fun _ _ => ⟨fun _ => inferInstance⟩, fun _ => ⟨fun _ => inferInstance⟩⟩
-/
lemma guitartExact_iff_final :
    w.GuitartExact ↔ forall (X₃ : C₃), (w.costructuredArrowRightwards X₃).Final :=
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, fun _ => ⟨fun _ => inferInstance⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hw
  signature: : w.GuitartExact] (X₃ : C₃) :
  body: by
  rw [guitartExact_iff_final] at hw
  apply hw

中文:
实例 [hw
  签名: : w.GuitartExact] (X₃ : C₃) :
  定义体: by
  rw [guitartExact_iff_final] at hw
  apply hw

Depends on / 依赖: guitartExact_iff_final
-/
instance [hw : w.GuitartExact] (X₃ : C₃) :
    (w.costructuredArrowRightwards X₃).Final := by
  rw [guitartExact_iff_final] at hw
  apply hw

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `structuredArrowDownwards_initial_iff_of_iso` / 引理 `structuredArrowDownwards_initial_iff_of_iso`

English:
lemma structuredArrowDownwards_initial_iff_of_iso
  given: {X₂ X₂' : C₂} (e : X₂ ≅ X₂')
  proof: by
  rw [Functor.initial_iff_comp_equivalence _ (StructuredArrow.mapIso (R.mapIso e)).functor]; rw [Functor.initial_iff_equivalence_comp (StructuredArrow.mapIso e).functor]
  exact Functor.initial_natIso_iff
    (NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _)))

中文:
引理 structuredArrowDownwards_initial_iff_of_iso
  条件: {X₂ X₂' : C₂} (e : X₂ ≅ X₂')
  证明: by
  rw [Functor.initial_iff_comp_equivalence _ (StructuredArrow.mapIso (R.mapIso e)).functor]; rw [Functor.initial_iff_equivalence_comp (StructuredArrow.mapIso e).functor]
  exact Functor.initial_natIso_iff
    (NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _)))

Depends on / 依赖: Functor, Functor.initial_iff_comp_equivalence, Functor.initial_iff_equivalence_comp, Functor.initial_natIso_iff, Iso.refl, NatIso, NatIso.ofComponents, R.mapIso, StructuredArrow, StructuredArrow.isoMk, StructuredArrow.mapIso, functor, initial_iff_comp_equivalence, initial_iff_equivalence_comp, initial_natIso_iff, mapIso, ofComponents
-/
lemma structuredArrowDownwards_initial_iff_of_iso {X₂ X₂' : C₂} (e : X₂ ≅ X₂') :
    (w.structuredArrowDownwards X₂).Initial ↔
      (w.structuredArrowDownwards X₂').Initial := by
  rw [Functor.initial_iff_comp_equivalence _ (StructuredArrow.mapIso (R.mapIso e)).functor]; rw [Functor.initial_iff_equivalence_comp (StructuredArrow.mapIso e).functor]
  exact Functor.initial_natIso_iff
    (NatIso.ofComponents (fun _ => StructuredArrow.isoMk (Iso.refl _)))

/--
lemma `guitartExact_iff_initial` / 引理 `guitartExact_iff_initial`

English:
lemma guitartExact_iff_initial
  proof: ⟨fun _ _ => ⟨fun _ => inferInstance⟩, by
    rw [guitartExact_iff_isConnected_downwards]
    intros
    infer_instance⟩

中文:
引理 guitartExact_iff_initial
  证明: ⟨fun _ _ => ⟨fun _ => inferInstance⟩, by
    rw [guitartExact_iff_isConnected_downwards]
    intros
    infer_instance⟩

Depends on / 依赖: guitartExact_iff_isConnected_downwards, infer_instance, intros
-/
lemma guitartExact_iff_initial :
    w.GuitartExact ↔ forall (X₂ : C₂), (w.structuredArrowDownwards X₂).Initial :=
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, by
    rw [guitartExact_iff_isConnected_downwards]
    intros
    infer_instance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [hw
  signature: : w.GuitartExact] (X₂ : C₂) :
  body: by
  rw [guitartExact_iff_initial] at hw
  apply hw

中文:
实例 [hw
  签名: : w.GuitartExact] (X₂ : C₂) :
  定义体: by
  rw [guitartExact_iff_initial] at hw
  apply hw

Depends on / 依赖: guitartExact_iff_initial
-/
instance [hw : w.GuitartExact] (X₂ : C₂) :
    (w.structuredArrowDownwards X₂).Initial := by
  rw [guitartExact_iff_initial] at hw
  apply hw

set_option backward.isDefEq.respectTransparency false in
/-- When the left and right functors of a 2-square are equivalences, and the natural
transformation of the 2-square is an isomorphism, then the 2-square is Guitart exact. -/
instance (priority := 100) guitartExact_of_isEquivalence_of_isIso
    [L.IsEquivalence] [R.IsEquivalence] [IsIso w.natTrans] : GuitartExact w := by
  rw [guitartExact_iff_initial]
  intro X₂
  have := StructuredArrow.isEquivalence_post X₂ T R
  have : (Comma.mapRight _ w : StructuredArrow (R.obj X₂) _ ⥤ _).IsEquivalence :=
    (Comma.mapRightIso _ (asIso w)).isEquivalence_functor
  have := StructuredArrow.isEquivalence_pre (R.obj X₂) L B
  dsimp only [structuredArrowDownwards]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `guitartExact_id` / 实例 `guitartExact_id`

English:
instance guitartExact_id
  signature: (F : C₁ ⥤ C₂)
  body: by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ (g : F.obj X₂ ⟶ X₃)
  let Z := StructuredArrowRightwards (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) g
  let X₀ : Z := StructuredArrow.mk (Y := CostructuredArrow.mk g) (CostructuredArrow.homMk (𝟙 _))
  have φ : forall (X : Z), X₀ ⟶ X := fun 

中文:
实例 guitartExact_id
  签名: (F : C₁ ⥤ C₂)
  定义体: by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ (g : F.obj X₂ ⟶ X₃)
  let Z := StructuredArrowRightwards (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) g
  let X₀ : Z := StructuredArrow.mk (Y := CostructuredArrow.mk g) (CostructuredArrow.homMk (𝟙 _))
  have φ : forall (X : Z), X₀ ⟶ X := fun 

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.mk, CostructuredArrow.w, F.obj, Nonempty, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk, StructuredArrowRightwards, TwoSquare, TwoSquare.mk, X.hom, X.hom.left, Zigzag, Zigzag.of_inv_hom, guitartExact_iff_isConnected_rightwards, of_inv_hom, zigzag_isConnected
-/
instance guitartExact_id (F : C₁ ⥤ C₂) :
    GuitartExact (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ (g : F.obj X₂ ⟶ X₃)
  let Z := StructuredArrowRightwards (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) g
  let X₀ : Z := StructuredArrow.mk (Y := CostructuredArrow.mk g) (CostructuredArrow.homMk (𝟙 _))
  have φ : forall (X : Z), X₀ ⟶ X := fun X =>
    StructuredArrow.homMk (CostructuredArrow.homMk X.hom.left
      (by simpa using! CostructuredArrow.w X.hom))
  have : Nonempty Z := ⟨X₀⟩
  apply zigzag_isConnected
  intro X Y
  exact Zigzag.of_inv_hom (φ X) (φ Y)

end TwoSquare

end CategoryTheory
