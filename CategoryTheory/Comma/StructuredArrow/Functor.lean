/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Grothendieck

/-!
# Structured Arrow Categories as strict functor to Cat

Forming a structured arrow category `StructuredArrow d T` with `d : D` and `T : C ⥤ D` is strictly
functorial in `S`, inducing a functor `Dᵒᵖ ⥤ Cat`. This file constructs said functor and proves
that, in the dual case, we can precompose it with another functor `L : E ⥤ D` to obtain a category
equivalent to `Comma L T`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace StructuredArrow

set_option backward.isDefEq.respectTransparency false in
/-- The structured arrow category `StructuredArrow d T` depends on the chosen domain `d : D` in a
functorial way, inducing a functor `Dᵒᵖ ⥤ Cat`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (T : C ⥤ D)
  body: .of StructuredArrow d.unop T
  map f := (map f.unop).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp)
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp)

中文:
定义 functor
  签名: (T : C ⥤ D)
  定义体: .of StructuredArrow d.unop T
  map f := (map f.unop).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp)
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp)

Depends on / 依赖: StructuredArrow, d.unop
-/
def functor (T : C ⥤ D) : Dᵒᵖ ⥤ Cat where
obj d := .of StructuredArrow d.unop T
  map f := (map f.unop).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp)
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp)

end StructuredArrow

namespace CostructuredArrow

set_option backward.isDefEq.respectTransparency false in
/-- The costructured arrow category `CostructuredArrow T d` depends on the chosen codomain `d : D`
in a functorial way, inducing a functor `D ⥤ Cat`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: (T : C ⥤ D)
  body: .of CostructuredArrow T d
  map f := (CostructuredArrow.map f).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

中文:
定义 functor
  签名: (T : C ⥤ D)
  定义体: .of CostructuredArrow T d
  map f := (CostructuredArrow.map f).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

Depends on / 依赖: CostructuredArrow
-/
def functor (T : C ⥤ D) : D ⥤ Cat where
obj d := .of CostructuredArrow T d
  map f := (CostructuredArrow.map f).toCatHom
  map_id d := by
    ext
    exact Functor.ext (fun ⟨_, _, _⟩ => by simp [CostructuredArrow.map, Comma.mapRight])
  map_comp f g := by
    ext
    exact Functor.ext (fun _ => by simp [CostructuredArrow.map, Comma.mapRight])

variable {E : Type u₃} [Category.{v₃} E]
variable (L : C ⥤ D) (R : E ⥤ D)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor used to establish the equivalence `grothendieckPrecompFunctorEquivalence` between
the Grothendieck construction on `CostructuredArrow.functor` and the comma category. -/
@[simps]
/--
Definition of `grothendieckPrecompFunctorToComma` / `grothendieckPrecompFunctorToComma` 的定义

English:
definition grothendieckPrecompFunctorToComma
  signature: : Grothendieck (R ⋙ functor L) ⥤ Comma L R where
  body: ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, by simp⟩

中文:
定义 grothendieckPrecompFunctorToComma
  签名: : Grothendieck (R ⋙ functor L) ⥤ 交换a L R where
  定义体: ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, by simp⟩

Depends on / 依赖: P.base, P.fiber.hom, P.fiber.left
-/
def grothendieckPrecompFunctorToComma : Grothendieck (R ⋙ functor L) ⥤ Comma L R where
  obj P := ⟨P.fiber.left, P.base, P.fiber.hom⟩
  map f := ⟨f.fiber.left, f.base, by simp⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Fibers of `grothendieckPrecompFunctorToComma L R`, composed with `Comma.fst L R`, are isomorphic
to the projection `proj L (R.obj X)`. -/
@[simps!]
/--
Definition of `ιCompGrothendieckPrecompFunctorToCommaCompFst` / `ιCompGrothendieckPrecompFunctorToCommaCompFst` 的定义

English:
definition ιCompGrothendieckPrecompFunctorToCommaCompFst
  signature: (X : E)
  body: NatIso.ofComponents (fun X => Iso.refl _) (fun _ => by simp)

中文:
定义 ιCompGrothendieckPrecompFunctorToCommaCompFst
  签名: (X : E)
  定义体: NatIso.ofComponents (fun X => Iso.refl _) (fun _ => by simp)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def ιCompGrothendieckPrecompFunctorToCommaCompFst (X : E) :
    Grothendieck.ι (R ⋙ functor L) X ⋙ grothendieckPrecompFunctorToComma L R ⋙ Comma.fst _ _ ≅
    proj L (R.obj X) :=
  NatIso.ofComponents (fun X => Iso.refl _) (fun _ => by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse functor used to establish the equivalence `grothendieckPrecompFunctorEquivalence`
between the Grothendieck construction on `CostructuredArrow.functor` and the comma category. -/
@[simps]
/--
Definition of `commaToGrothendieckPrecompFunctor` / `commaToGrothendieckPrecompFunctor` 的定义

English:
definition commaToGrothendieckPrecompFunctor
  signature: : Comma L R ⥤ Grothendieck (R ⋙ functor L) where
  body: ⟨X.right, mk X.hom⟩
  map f := ⟨f.right, homMk f.left⟩
  map_id X := Grothendieck.ext _ _ rfl (by simp)
  map_comp f g := Grothendieck.ext _ _ rfl (by simp)

中文:
定义 commaToGrothendieckPrecompFunctor
  签名: : 交换a L R ⥤ Grothendieck (R ⋙ functor L) where
  定义体: ⟨X.right, mk X.hom⟩
  map f := ⟨f.right, homMk f.left⟩
  map_id X := Grothendieck.ext _ _ rfl (by simp)
  map_comp f g := Grothendieck.ext _ _ rfl (by simp)

Depends on / 依赖: X.hom, X.right
-/
def commaToGrothendieckPrecompFunctor : Comma L R ⥤ Grothendieck (R ⋙ functor L) where
  obj X := ⟨X.right, mk X.hom⟩
  map f := ⟨f.right, homMk f.left⟩
  map_id X := Grothendieck.ext _ _ rfl (by simp)
  map_comp f g := Grothendieck.ext _ _ rfl (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- For `L : C ⥤ D`, taking the Grothendieck construction of `CostructuredArrow.functor L`
precomposed with another functor `R : E ⥤ D` results in a category which is equivalent to
the comma category `Comma L R`. -/
@[simps]
/--
Definition of `grothendieckPrecompFunctorEquivalence` / `grothendieckPrecompFunctorEquivalence` 的定义

English:
definition grothendieckPrecompFunctorEquivalence
  signature: : Grothendieck (R ⋙ functor L) ≌ Comma L R where
  body: grothendieckPrecompFunctorToComma _ _
  inverse := commaToGrothendieckPrecompFunctor _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 grothendieckPrecompFunctorEquivalence
  签名: : Grothendieck (R ⋙ functor L) ≌ 交换a L R where
  定义体: grothendieckPrecompFunctorToComma _ _
  inverse := commaToGrothendieckPrecompFunctor _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: grothendieckPrecompFunctorToComma
-/
def grothendieckPrecompFunctorEquivalence : Grothendieck (R ⋙ functor L) ≌ Comma L R where
  functor := grothendieckPrecompFunctorToComma _ _
  inverse := commaToGrothendieckPrecompFunctor _ _
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/-- The functor projecting out the domain of arrows from the Grothendieck construction on
costructured arrows. -/
@[simps!]
/--
Definition of `grothendieckProj` / `grothendieckProj` 的定义

English:
definition grothendieckProj
  signature: : Grothendieck (functor L) ⥤ C
  body: grothendieckPrecompFunctorToComma L (𝟭 _) ⋙ Comma.fst _ _

#adaptation_note

中文:
定义 grothendieckProj
  签名: : Grothendieck (functor L) ⥤ C
  定义体: grothendieckPrecompFunctorToComma L (𝟭 _) ⋙ Comma.fst _ _

#adaptation_note

Depends on / 依赖: Comma.fst, grothendieckPrecompFunctorToComma
-/
def grothendieckProj : Grothendieck (functor L) ⥤ C :=
  grothendieckPrecompFunctorToComma L (𝟭 _) ⋙ Comma.fst _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`. -/
@[simps!]
/--
Definition of `ιCompGrothendieckProj` / `ιCompGrothendieckProj` 的定义

English:
definition ιCompGrothendieckProj
  signature: (X : D)
  body: ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) X

#adaptation_note

中文:
定义 ιCompGrothendieckProj
  签名: (X : D)
  定义体: ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) X

#adaptation_note
-/
def ιCompGrothendieckProj (X : D) :
    Grothendieck.ι (functor L) X ⋙ grothendieckProj L ≅ proj L X :=
  ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) X

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Functors between costructured arrow categories induced by morphisms in the base category
composed with fibers of `grothendieckProj L` are isomorphic to the projection `proj L X`. -/
@[simps!]
/--
Definition of `mapCompιCompGrothendieckProj` / `mapCompιCompGrothendieckProj` 的定义

English:
definition mapCompιCompGrothendieckProj
  signature: {X Y : D} (f : X ⟶ Y)
  body: Functor.isoWhiskerLeft (CostructuredArrow.map f)
    (ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) Y)

中文:
定义 mapCompιCompGrothendieckProj
  签名: {X Y : D} (f : X ⟶ Y)
  定义体: Functor.isoWhiskerLeft (CostructuredArrow.map f)
    (ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) Y)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, Functor, Functor.isoWhiskerLeft, Ind.inclusion, Ind.lim, Ind.limCompInclusion.symm, PreservesLimitsOfShape, inclusion, isoWhiskerLeft, limCompInclusion, preservesLimitsOfShape_of_natIso, preservesLimitsOfShape_of_reflects_of_preserves
-/
def mapCompιCompGrothendieckProj {X Y : D} (f : X ⟶ Y) :
    CostructuredArrow.map f ⋙ Grothendieck.ι (functor L) Y ⋙ grothendieckProj L ≅ proj L X :=
  Functor.isoWhiskerLeft (CostructuredArrow.map f)
    (ιCompGrothendieckPrecompFunctorToCommaCompFst L (𝟭 _) Y)

/-- The functor `CostructuredArrow.pre` induces a natural transformation
`CostructuredArrow.functor (S ⋙ T) ⟶ CostructuredArrow.functor T` for `S : C ⥤ D` and
`T : D ⥤ E`. -/
@[simps]
/--
Definition of `preFunctor` / `preFunctor` 的定义

English:
definition preFunctor
  signature: {D : Type u₁} [Category.{v₁} D] (S : C ⥤ D) (T : D ⥤ E)
  body: (pre S T e).toCatHom

中文:
定义 preFunctor
  签名: {D : 类型u₁} [范畴.{v₁} D] (S : C ⥤ D) (T : D ⥤ E)
  定义体: (pre S T e).toCatHom

Depends on / 依赖: PreservesColimitsOfShape, toCatHom
-/
def preFunctor {D : Type u₁} [Category.{v₁} D] (S : C ⥤ D) (T : D ⥤ E) :
    functor (S ⋙ T) ⟶ functor T where
  app e := (pre S T e).toCatHom

end CostructuredArrow

end CategoryTheory
