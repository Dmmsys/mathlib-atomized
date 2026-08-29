/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Functor.CurryingThree

/-!

# Constructing braided categories from natural transformations between multifunctors

This file provides an alternative constructor for braided categories, given a braiding
`β : -₁ ⊗ -₂ ≅ -₂ ⊗ -₁` as a natural isomorphism between bifunctors. The hexagon identities are
phrased as equalities of natural transformations between trifunctors
`(-₁ ⊗ -₂) ⊗ -₃ ⟶ -₂ ⊗ (-₃ ⊗ -₁)` and `-₁ ⊗ (-₂ ⊗ -₃) ⟶ (-₃ ⊗ -₁) ⊗ -₂`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C]

open MonoidalCategory CategoryTheory.Functor

namespace BraidedCategory

namespace Hexagon

variable (C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₂) ⊗ X₃` -/
@[simps!]
/--
Definition of `functor₁₂₃` / `functor₁₂₃` 的定义

English:
definition functor₁₂₃
  signature: : C ⥤ C ⥤ C ⥤ C
  body: bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

中文:
定义 functor₁₂₃
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

Depends on / 依赖: curriedTensor
-/
def functor₁₂₃ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₂ ⊗ X₃)` -/
@[simps!]
/--
Definition of `functor₁₂₃'` / `functor₁₂₃'` 的定义

English:
definition functor₁₂₃'
  signature: : C ⥤ C ⥤ C ⥤ C
  body: bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

中文:
定义 functor₁₂₃'
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

Depends on / 依赖: curriedTensor
-/
def functor₁₂₃' : C ⥤ C ⥤ C ⥤ C := bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₃) ⊗ X₁` -/
@[simps!]
/--
Definition of `functor₂₃₁` / `functor₂₃₁` 的定义

English:
definition functor₂₃₁
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

中文:
定义 functor₂₃₁
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

Depends on / 依赖: curriedTensor
-/
def functor₂₃₁ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C))

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₃ ⊗ X₁)` -/
@[simps!]
/--
Definition of `functor₂₃₁'` / `functor₂₃₁'` 的定义

English:
definition functor₂₃₁'
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

中文:
定义 functor₂₃₁'
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

Depends on / 依赖: curriedTensor, flip.flip
-/
def functor₂₃₁' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₁₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₂ ⊗ X₁) ⊗ X₃` -/
@[simps!]
/--
Definition of `functor₂₁₃` / `functor₂₁₃` 的定义

English:
definition functor₂₁₃
  signature: : C ⥤ C ⥤ C ⥤ C
  body: bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

中文:
定义 functor₂₁₃
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

Depends on / 依赖: curriedTensor
-/
def functor₂₁₃ : C ⥤ C ⥤ C ⥤ C := bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)

/-- The trifunctor `X₁ X₂ X₃ ↦ X₂ ⊗ (X₁ ⊗ X₃)` -/
@[simps!]
/--
Definition of `functor₂₁₃'` / `functor₂₁₃'` 的定义

English:
definition functor₂₁₃'
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

中文:
定义 functor₂₁₃'
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

Depends on / 依赖: curriedTensor
-/
def functor₂₁₃' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip

/-- The trifunctor `X₁ X₂ X₃ ↦ X₃ ⊗ (X₁ ⊗ X₂)` -/
@[simps!]
/--
Definition of `functor₃₁₂'` / `functor₃₁₂'` 的定义

English:
definition functor₃₁₂'
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

中文:
定义 functor₃₁₂'
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

Depends on / 依赖: curriedTensor, flip.flip
-/
def functor₃₁₂' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₃ ⊗ X₁) ⊗ X₂` -/
@[simps!]
/--
Definition of `functor₃₁₂` / `functor₃₁₂` 的定义

English:
definition functor₃₁₂
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

中文:
定义 functor₃₁₂
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

Depends on / 依赖: curriedTensor, flip.flip
-/
def functor₃₁₂ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip.flip₂₃

/-- The trifunctor `X₁ X₂ X₃ ↦ X₁ ⊗ (X₃ ⊗ X₂)` -/
@[simps!]
/--
Definition of `functor₁₃₂'` / `functor₁₃₂'` 的定义

English:
definition functor₁₃₂'
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip)

中文:
定义 functor₁₃₂'
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip)

Depends on / 依赖: curriedTensor
-/
def functor₁₃₂' : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip)

/-- The trifunctor `X₁ X₂ X₃ ↦ (X₁ ⊗ X₃) ⊗ X₂` -/
@[simps!]
/--
Definition of `functor₁₃₂` / `functor₁₃₂` 的定义

English:
definition functor₁₃₂
  signature: : C ⥤ C ⥤ C ⥤ C
  body: (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip₂₃

中文:
定义 functor₁₃₂
  签名: : C ⥤ C ⥤ C ⥤ C
  定义体: (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip₂₃

Depends on / 依赖: curriedTensor
-/
def functor₁₃₂ : C ⥤ C ⥤ C ⥤ C := (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip₂₃

end Hexagon

open Hexagon

namespace ofBifunctor

-- We use the following three defeq abuses, together with `F.flip.flip = F`
example : (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)).flip =
    (bifunctorComp₁₂ (curriedTensor C).flip (curriedTensor C)) := by
  rfl

example : (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C)).flip =
    (bifunctorComp₂₃ (curriedTensor C) (curriedTensor C).flip).flip.flip₁₃ := by
  rfl

example : (bifunctorComp₁₂ (curriedTensor C) (curriedTensor C)) =
    (bifunctorComp₂₃ (curriedTensor C).flip (curriedTensor C)).flip.flip₂₃ := by
  rfl

namespace Forward

/-!

### The forward hexagon identity

Given a braiding in the form of a natural isomorphism of bifunctors
`β : curriedTensor C ≅ (curriedTensor C).flip` (i.e. `(β.app X₁).app X₂ : X₁ ⊗ X₂ ≅ X₂ ⊗ X₁`),
we phrase the forward hexagon identity as an equality of natural transformations between trifunctors
(the hexagon on the left is the diagram we require to commute, the hexagon on the right is the
same on the object level on three objects `X₁ X₂ X₃`).

```
            functor₁₂₃ (X₁ ⊗ X₂) ⊗ X₃
associator / \ secondMap₁ / \
          v v v v
     functor₁₂₃' functor₂₁₃ X₁ ⊗ (X₂ ⊗ X₃) (X₂ ⊗ X₁) ⊗ X₃
firstMap₂ | |secondMap₂ | |
          v v v v
     functor₂₃₁ functor₂₁₃' (X₂ ⊗ X₃) ⊗ X₁ X₂ ⊗ (X₁ ⊗ X₃)
  firstMap₃\ / secondMap₃ \ /
            v v v v
             functor₂₃₁' X₂ ⊗ (X₃ ⊗ X₁)
```
-/

/-- The middle left map in the forward hexagon identity. -/
@[simps!]
/--
Definition of `firstMap₂` / `firstMap₂` 的定义

English:
definition firstMap₂
  signature: (β : curriedTensor C ≅ (curriedTensor C).flip)
  body: (bifunctorComp₂₃Functor.map β.hom).app _

中文:
定义 firstMap₂
  签名: (β : curriedTensor C ≅ (curriedTensor C).flip)
  定义体: (bifunctorComp₂₃Functor.map β.hom).app _

Depends on / 依赖: Functor.map
-/
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃' C ⟶ functor₂₃₁ C :=
  (bifunctorComp₂₃Functor.map β.hom).app _

variable (C) in
/-- The bottom left map in the forward hexagon identity. -/
@[simps!]
/--
Definition of `firstMap₃` / `firstMap₃` 的定义

English:
definition firstMap₃
  signature: : functor₂₃₁ C ⟶ functor₂₃₁' C where
  body: { app _ := { app _ := (α_ _ _ _).hom } }

#adaptation_note

中文:
定义 firstMap₃
  签名: : functor₂₃₁ C ⟶ functor₂₃₁' C where
  定义体: { app _ := { app _ := (α_ _ _ _).hom } }

#adaptation_note
-/
def firstMap₃ : functor₂₃₁ C ⟶ functor₂₃₁' C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The top right map in the forward hexagon identity. -/
@[simps!]
/--
Definition of `secondMap₁` / `secondMap₁` 的定义

English:
definition secondMap₁
  signature: (β : curriedTensor C ≅ (curriedTensor C).flip)
  body: (bifunctorComp₁₂Functor.map β.hom).app _

中文:
定义 secondMap₁
  签名: (β : curriedTensor C ≅ (curriedTensor C).flip)
  定义体: (bifunctorComp₁₂Functor.map β.hom).app _

Depends on / 依赖: Functor.map
-/
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃ C ⟶ functor₂₁₃ C :=
  (bifunctorComp₁₂Functor.map β.hom).app _

variable (C) in
/-- The middle right map in the forward hexagon identity. -/
@[simps!]
/--
Definition of `secondMap₂` / `secondMap₂` 的定义

English:
definition secondMap₂
  signature: : functor₂₁₃ C ⟶ functor₂₁₃' C where
  body: { app _ := { app _ := (α_ _ _ _).hom } }

#adaptation_note

中文:
定义 secondMap₂
  签名: : functor₂₁₃ C ⟶ functor₂₁₃' C where
  定义体: { app _ := { app _ := (α_ _ _ _).hom } }

#adaptation_note
-/
def secondMap₂ : functor₂₁₃ C ⟶ functor₂₁₃' C where
  app _ := { app _ := { app _ := (α_ _ _ _).hom } }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The bottom right map in the forward hexagon identity. -/
@[simps!]
/--
Definition of `secondMap₃` / `secondMap₃` 的定义

English:
definition secondMap₃
  signature: (β : curriedTensor C ≅ (curriedTensor C).flip)
  body: flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))

中文:
定义 secondMap₃
  签名: (β : curriedTensor C ≅ (curriedTensor C).flip)
  定义体: flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))

Depends on / 依赖: Functor.map, Functor.obj, curriedTensor, flipFunctor
-/
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₂₁₃' C ⟶ functor₂₃₁' C :=
  flip₁₃Functor.map ((flipFunctor _ _ _).map
    ((bifunctorComp₂₃Functor.obj (curriedTensor C)).map ((flipFunctor _ _ _).map β.hom)))

end Forward

namespace Reverse

/-!

### The reverse hexagon identity

Given a braiding in the form of a natural isomorphism of bifunctors
`β : curriedTensor C ≅ (curriedTensor C).flip` (i.e. `(β.app X₁).app X₂ : X₁ ⊗ X₂ ≅ X₂ ⊗ X₁`),
we phrase the reverse hexagon identity as an equality of natural transformations between trifunctors
(the hexagon on the left is the diagram we require to commute, the hexagon on the right is the
same on the object level on three objects `X₁ X₂ X₃`).

```
            functor₁₂₃' X₁ ⊗ (X₂ ⊗ X₃)
associator / \ secondMap₁ / \
          v v v v
     functor₁₂₃ functor₁₃₂' (X₁ ⊗ X₂) ⊗ X₃ X₁ ⊗ (X₃ ⊗ X₂)
firstMap₂ | |secondMap₂ | |
          v v v v
     functor₃₁₂' functor₁₃₂ X₃ ⊗ (X₁ ⊗ X₂) (X₁ ⊗ X₃) ⊗ X₂
  firstMap₃\ / secondMap₃ \ /
            v v v v
             functor₃₁₂ (X₃ ⊗ X₁) ⊗ X₂
```
-/

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The middle left map in the reverse hexagon identity. -/
@[simps!]
/--
Definition of `firstMap₂` / `firstMap₂` 的定义

English:
definition firstMap₂
  signature: (β : curriedTensor C ≅ (curriedTensor C).flip)
  body: flip₂₃Functor.map ((flipFunctor _ _ _).map ((bifunctorComp₂₃Functor.map
    ((flipFunctor _ _ _).map β.hom)).app _))

中文:
定义 firstMap₂
  签名: (β : curriedTensor C ≅ (curriedTensor C).flip)
  定义体: flip₂₃Functor.map ((flipFunctor _ _ _).map ((bifunctorComp₂₃Functor.map
    ((flipFunctor _ _ _).map β.hom)).app _))

Depends on / 依赖: Functor.map, flipFunctor
-/
def firstMap₂ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃ C ⟶ functor₃₁₂' C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map ((bifunctorComp₂₃Functor.map
    ((flipFunctor _ _ _).map β.hom)).app _))

variable (C) in
/-- The bottom left map in the reverse hexagon identity. -/
@[simps!]
/--
Definition of `firstMap₃` / `firstMap₃` 的定义

English:
definition firstMap₃
  signature: : functor₃₁₂' C ⟶ functor₃₁₂ C
  body: flip₂₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).inv)

#adaptation_note

中文:
定义 firstMap₃
  签名: : functor₃₁₂' C ⟶ functor₃₁₂ C
  定义体: flip₂₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).inv)

#adaptation_note

Depends on / 依赖: Functor.map, curriedAssociatorNatIso, flipFunctor
-/
def firstMap₃ : functor₃₁₂' C ⟶ functor₃₁₂ C :=
  flip₂₃Functor.map ((flipFunctor _ _ _).map (curriedAssociatorNatIso C).inv)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The top right map in the reverse hexagon identity. -/
@[simps!]
/--
Definition of `secondMap₁` / `secondMap₁` 的定义

English:
definition secondMap₁
  signature: (β : curriedTensor C ≅ (curriedTensor C).flip)
  body: (bifunctorComp₂₃Functor.obj _).map β.hom

中文:
定义 secondMap₁
  签名: (β : curriedTensor C ≅ (curriedTensor C).flip)
  定义体: (bifunctorComp₂₃Functor.obj _).map β.hom

Depends on / 依赖: Functor.obj
-/
def secondMap₁ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₂₃' C ⟶ functor₁₃₂' C :=
  (bifunctorComp₂₃Functor.obj _).map β.hom

variable (C) in
/-- The middle right map in the reverse hexagon identity. -/
@[simps!]
/--
Definition of `secondMap₂` / `secondMap₂` 的定义

English:
definition secondMap₂
  signature: : functor₁₃₂' C ⟶ functor₁₃₂ C where
  body: { app _ := { app _ := (α_ _ _ _).inv } }

#adaptation_note

中文:
定义 secondMap₂
  签名: : functor₁₃₂' C ⟶ functor₁₃₂ C where
  定义体: { app _ := { app _ := (α_ _ _ _).inv } }

#adaptation_note
-/
def secondMap₂ : functor₁₃₂' C ⟶ functor₁₃₂ C where
  app _ := { app _ := { app _ := (α_ _ _ _).inv } }

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The bottom right map in the reverse hexagon identity. -/
@[simps!]
/--
Definition of `secondMap₃` / `secondMap₃` 的定义

English:
definition secondMap₃
  signature: (β : curriedTensor C ≅ (curriedTensor C).flip)
  body: flip₂₃Functor.map ((bifunctorComp₁₂Functor.map β.hom).app _)

中文:
定义 secondMap₃
  签名: (β : curriedTensor C ≅ (curriedTensor C).flip)
  定义体: flip₂₃Functor.map ((bifunctorComp₁₂Functor.map β.hom).app _)

Depends on / 依赖: Functor.map
-/
def secondMap₃ (β : curriedTensor C ≅ (curriedTensor C).flip) : functor₁₃₂ C ⟶ functor₃₁₂ C :=
  flip₂₃Functor.map ((bifunctorComp₁₂Functor.map β.hom).app _)

end Reverse

end ofBifunctor

open ofBifunctor

variable (β : curriedTensor C ≅ (curriedTensor C).flip)
  (hexagon_forward : (curriedAssociatorNatIso C).hom ≫
    Forward.firstMap₂ β ≫ Forward.firstMap₃ C =
    Forward.secondMap₁ β ≫ Forward.secondMap₂ C ≫ Forward.secondMap₃ β)
  (hexagon_reverse : (curriedAssociatorNatIso C).inv ≫
    Reverse.firstMap₂ β ≫ Reverse.firstMap₃ C =
    Reverse.secondMap₁ β ≫ Reverse.secondMap₂ C ≫ Reverse.secondMap₃ β)

/--
Given a braiding `β : curriedTensor C ≅ (curriedTensor C).flip` as a natural isomorphism between
bifunctors, and the two equalities `hexagon_forward` and `hexagon_reverse` of natural
transformations between trifunctors, we obtain a braided category structure.
-/
@[instance_reducible]
/--
Definition of `ofBifunctor` / `ofBifunctor` 的定义

English:
definition ofBifunctor
  signature: : BraidedCategory C where
  body: (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse X Y Z :=
 

中文:
定义 ofBifunctor
  签名: : 辫范畴 C where
  定义体: (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse X Y Z :=
 
-/
def ofBifunctor : BraidedCategory C where
  braiding X Y := (β.app X).app Y
  braiding_naturality_right _ _ _ _ := (β.app _).hom.naturality _
  braiding_naturality_left _ _ := NatTrans.congr_app (β.hom.naturality _) _
  hexagon_forward X Y Z :=
    NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_forward X) Y) Z
  hexagon_reverse X Y Z :=
    (NatTrans.congr_app (NatTrans.congr_app (NatTrans.congr_app hexagon_reverse X) Y) Z)

end BraidedCategory

open BraidedCategory

/--
Alternative constructor for symmetric categories, where the symmetry of the braiding is phrased
as an equality of natural transformation of bifunctors.
-/
@[instance_reducible]
/--
Definition of `SymmetricCategory.ofCurried` / `SymmetricCategory.ofCurried` 的定义

English:
definition SymmetricCategory.ofCurried
  signature: [BraidedCategory C]
  body: NatTrans.congr_app (NatTrans.congr_app h X) Y

中文:
定义 对称范畴.ofCurried
  签名: [辫范畴 C]
  定义体: NatTrans.congr_app (NatTrans.congr_app h X) Y

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app
-/
def SymmetricCategory.ofCurried [BraidedCategory C]
    (h : (curriedBraidingNatIso C).hom ≫ (flipFunctor _ _ _).map (curriedBraidingNatIso C).hom =
      𝟙 _) :
    SymmetricCategory C where
  symmetry X Y := NatTrans.congr_app (NatTrans.congr_app h X) Y

end CategoryTheory
