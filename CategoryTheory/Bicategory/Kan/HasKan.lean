/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Bicategory.Kan.IsKan

/-!
# Existence of Kan extensions and Kan lifts in bicategories

We provide the propositional typeclass `HasLeftKanExtension f g`, which asserts that there
exists a left Kan extension of `g` along `f`. See `CategoryTheory.Bicategory.Kan.IsKan` for
the definition of left Kan extensions. Under the assumption that `HasLeftKanExtension f g`,
we define the left Kan extension `lan f g` by using the axiom of choice.

## Main definitions

* `lan f g` is the left Kan extension of `g` along `f`, and is denoted by `f⁺ g`.
* `lanLift f g` is the left Kan lift of `g` along `f`, and is denoted by `f₊ g`.

These notations are inspired by
[M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006].

## TODO

* `ran f g` is the right Kan extension of `g` along `f`, and is denoted by `f⁺⁺ g`.
* `ranLift f g` is the right Kan lift of `g` along `f`, and is denoted by `f₊₊ g`.

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

open Limits

section LeftKan

open LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/--
Definition of `HasLeftKanExtension` / `HasLeftKanExtension` 的定义

English:
class HasLeftKanExtension
  parameters: (f : a ⟶ b) (g : a ⟶ c)
  axioms and operations (1):
    - hasInitial : HasInitial LeftExtension f g

中文:
类 HasLeftKanExtension
  参数: (f : a ⟶ b) (g : a ⟶ c)
  公理与运算 (1 个):
    - hasInitial : HasInitial LeftExtension f g
-/
class HasLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop where
hasInitial : HasInitial LeftExtension f g

/--
theorem `LeftExtension.IsKan.hasLeftKanExtension` / 定理 `LeftExtension.IsKan.hasLeftKanExtension`

English:
theorem LeftExtension.IsKan.hasLeftKanExtension
  given: {t : LeftExtension f g} (H : IsKan t)
  proof: ⟨IsInitial.hasInitial H⟩

中文:
定理 LeftExtension.IsKan.hasLeftKanExtension
  条件: {t : LeftExtension f g} (H : IsKan t)
  证明: ⟨IsInitial.hasInitial H⟩

Depends on / 依赖: IsInitial, IsInitial.hasInitial, hasInitial
-/
theorem LeftExtension.IsKan.hasLeftKanExtension {t : LeftExtension f g} (H : IsKan t) :
    HasLeftKanExtension f g :=
  ⟨IsInitial.hasInitial H⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLeftKanExtension
  signature: f g] : HasInitial LeftExtension f g
  body: HasLeftKanExtension.hasInitial

中文:
实例 [HasLeftKanExtension
  签名: f g] : HasInitial LeftExtension f g
  定义体: HasLeftKanExtension.hasInitial

Depends on / 依赖: HasLeftKanExtension, HasLeftKanExtension.hasInitial, hasInitial
-/
instance [HasLeftKanExtension f g] : HasInitial LeftExtension f g :=
  HasLeftKanExtension.hasInitial

/--
Definition of `lanLeftExtension` / `lanLeftExtension` 的定义

English:
definition lanLeftExtension
  signature: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  body: ⊥_ (LeftExtension f g)

中文:
定义 lanLeftExtension
  签名: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  定义体: ⊥_ (LeftExtension f g)

Depends on / 依赖: LeftExtension
-/
def lanLeftExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftExtension f g :=
  ⊥_ (LeftExtension f g)

/--
Definition of `lan` / `lan` 的定义

English:
definition lan
  signature: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  body: (lanLeftExtension f g).extension

中文:
定义 lan
  签名: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  定义体: (lanLeftExtension f g).extension

Depends on / 依赖: extension, lanLeftExtension
-/
def lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c :=
  (lanLeftExtension f g).extension

/-- `f⁺ g` is the left Kan extension of `g` along `f`.
```
  b
  △ \
  | \ f⁺ g
f | \
  | ◿
  a - - - ▷ c
      g
```
-/
scoped infixr:90 "⁺ " => lan

@[simp]
/--
theorem `lanLeftExtension_extension` / 定理 `lanLeftExtension_extension`

English:
theorem lanLeftExtension_extension
  given: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  proof: rfl

中文:
定理 lanLeftExtension_extension
  条件: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  证明: rfl
-/
theorem lanLeftExtension_extension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (lanLeftExtension f g).extension = f⁺ g := rfl

/--
Definition of `lanUnit` / `lanUnit` 的定义

English:
definition lanUnit
  signature: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  body: (lanLeftExtension f g).unit

@[simp]

中文:
定义 lanUnit
  签名: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  定义体: (lanLeftExtension f g).unit

@[simp]

Depends on / 依赖: lanLeftExtension
-/
def lanUnit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : g ⟶ f ≫ f⁺ g :=
  (lanLeftExtension f g).unit

@[simp]
/--
theorem `lanLeftExtension_unit` / 定理 `lanLeftExtension_unit`

English:
theorem lanLeftExtension_unit
  given: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  proof: rfl

中文:
定理 lanLeftExtension_unit
  条件: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  证明: rfl

Depends on / 依赖: preservesLimit_of_createsLimit_and_hasLimit
-/
theorem lanLeftExtension_unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (lanLeftExtension f g).unit = lanUnit f g := rfl

/--
Definition of `lanIsKan` / `lanIsKan` 的定义

English:
definition lanIsKan
  signature: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  body: initialIsInitial

中文:
定义 lanIsKan
  签名: (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
  定义体: initialIsInitial

Depends on / 依赖: initialIsInitial, preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape
-/
def lanIsKan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : (lanLeftExtension f g).IsKan :=
  initialIsInitial

variable {f : a ⟶ b} {g : a ⟶ c}

/--
Definition of `lanDesc` / `lanDesc` 的定义

English:
definition lanDesc
  signature: [HasLeftKanExtension f g] (s : LeftExtension f g)
  body: (lanIsKan f g).desc s

@[reassoc (attr := simp)]

中文:
定义 lanDesc
  签名: [HasLeftKanExtension f g] (s : LeftExtension f g)
  定义体: (lanIsKan f g).desc s

@[reassoc (attr := simp)]

Depends on / 依赖: lanIsKan, preservesLimits_of_createsLimits_and_hasLimits
-/
def lanDesc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    f⁺ g ⟶ s.extension :=
  (lanIsKan f g).desc s

@[reassoc (attr := simp)]
/--
theorem `lanUnit_desc` / 定理 `lanUnit_desc`

English:
theorem lanUnit_desc
  given: [HasLeftKanExtension f g] (s : LeftExtension f g)
  proof: (lanIsKan f g).fac s

@[simp]

中文:
定理 lanUnit_desc
  条件: [HasLeftKanExtension f g] (s : LeftExtension f g)
  证明: (lanIsKan f g).fac s

@[simp]

Depends on / 依赖: lanIsKan
-/
theorem lanUnit_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    lanUnit f g ≫ f ◁ lanDesc s = s.unit :=
  (lanIsKan f g).fac s

@[simp]
/--
theorem `lanIsKan_desc` / 定理 `lanIsKan_desc`

English:
theorem lanIsKan_desc
  given: [HasLeftKanExtension f g] (s : LeftExtension f g)
  proof: rfl

中文:
定理 lanIsKan_desc
  条件: [HasLeftKanExtension f g] (s : LeftExtension f g)
  证明: rfl
-/
theorem lanIsKan_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    (lanIsKan f g).desc s = lanDesc s :=
  rfl

/--
theorem `Lan.existsUnique` / 定理 `Lan.existsUnique`

English:
theorem Lan.existsUnique
  given: [HasLeftKanExtension f g] (s : LeftExtension f g)
  proof: (lanIsKan f g).existsUnique _

中文:
定理 Lan.existsUnique
  条件: [HasLeftKanExtension f g] (s : LeftExtension f g)
  证明: (lanIsKan f g).existsUnique _

Depends on / 依赖: existsUnique, lanIsKan
-/
theorem Lan.existsUnique [HasLeftKanExtension f g] (s : LeftExtension f g) :
    exists! τ, lanUnit f g ≫ f ◁ τ = s.unit :=
  (lanIsKan f g).existsUnique _

/--
Definition of `Lan.CommuteWith` / `Lan.CommuteWith` 的定义

English:
class Lan.CommuteWith
  axioms and operations (1):
    - commute : Nonempty IsKan (lanLeftExtension f g).whisker h

中文:
类 Lan.CommuteWith
  公理与运算 (1 个):
    - commute : Nonempty IsKan (lanLeftExtension f g).whisker h
-/
class Lan.CommuteWith
    (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] {x : B} (h : c ⟶ x) : Prop where
commute : Nonempty IsKan (lanLeftExtension f g).whisker h

namespace Lan.CommuteWith

/--
theorem `of_isKan_whisker` / 定理 `of_isKan_whisker`

English:
theorem of_isKan_whisker
  statement: [HasLeftKanExtension f g] (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  proof: ⟨⟨IsKan.ofIsoKan H i⟩⟩

中文:
定理 of_isKan_whisker
  结论: [HasLeftKanExtension f g] (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  证明: ⟨⟨IsKan.ofIsoKan H i⟩⟩

Depends on / 依赖: IsKan.ofIsoKan, ofIsoKan
-/
theorem of_isKan_whisker [HasLeftKanExtension f g] (t : LeftExtension f g) {x : B} (h : c ⟶ x)
    (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLeftExtension f g).whisker h) :
    Lan.CommuteWith f g h :=
  ⟨⟨IsKan.ofIsoKan H i⟩⟩

/--
theorem `of_lan_comp_iso` / 定理 `of_lan_comp_iso`

English:
theorem of_lan_comp_iso
  statement: [HasLeftKanExtension f g]
  proof: ⟨⟨(lanIsKan f (g ≫ h)).ofIsoKan StructuredArrow.isoMk i⟩⟩

中文:
定理 of_lan_comp_iso
  结论: [HasLeftKanExtension f g]
  证明: ⟨⟨(lanIsKan f (g ≫ h)).ofIsoKan StructuredArrow.isoMk i⟩⟩

Depends on / 依赖: StructuredArrow, StructuredArrow.isoMk, lanIsKan, ofIsoKan
-/
theorem of_lan_comp_iso [HasLeftKanExtension f g]
    {x : B} {h : c ⟶ x} [HasLeftKanExtension f (g ≫ h)]
    (i : f⁺ (g ≫ h) ≅ f⁺ g ≫ h)
    (w : lanUnit f (g ≫ h) ≫ f ◁ i.hom = lanUnit f g ▷ h ≫ (α_ _ _ _).hom) :
    Lan.CommuteWith f g h :=
⟨⟨(lanIsKan f (g ≫ h)).ofIsoKan StructuredArrow.isoMk i⟩⟩

variable (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
variable {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h]

/--
Definition of `isKan` / `isKan` 的定义

English:
definition isKan
  signature: : IsKan (lanLeftExtension f g).whisker h
  body: Classical.choice Lan.CommuteWith.commute

中文:
定义 isKan
  签名: : IsKan (lanLeftExtension f g).whisker h
  定义体: Classical.choice Lan.CommuteWith.commute

Depends on / 依赖: Classical, Classical.choice, CommuteWith, Lan.CommuteWith.commute, choice, commute
-/
def isKan : IsKan (lanLeftExtension f g).whisker h := Classical.choice Lan.CommuteWith.commute

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLeftKanExtension f (g ≫ h)
  body: (Lan.CommuteWith.isKan f g h).hasLeftKanExtension

中文:
实例 :
  签名: HasLeftKanExtension f (g ≫ h)
  定义体: (Lan.CommuteWith.isKan f g h).hasLeftKanExtension

Depends on / 依赖: CommuteWith, Lan.CommuteWith.isKan, hasLeftKanExtension, preservesColimit_of_createsColimit_and_hasColimit
-/
instance : HasLeftKanExtension f (g ≫ h) := (Lan.CommuteWith.isKan f g h).hasLeftKanExtension

/--
Definition of `isKanWhisker` / `isKanWhisker` 的定义

English:
definition isKanWhisker
  body: IsKan.whiskerOfCommute (lanLeftExtension f g) t (IsKan.uniqueUpToIso (lanIsKan f g) H) h
    (isKan f g h)

中文:
定义 isKanWhisker
  定义体: IsKan.whiskerOfCommute (lanLeftExtension f g) t (IsKan.uniqueUpToIso (lanIsKan f g) H) h
    (isKan f g h)

Depends on / 依赖: IsKan.uniqueUpToIso, IsKan.whiskerOfCommute, lanIsKan, lanLeftExtension, preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape, uniqueUpToIso, whiskerOfCommute
-/
def isKanWhisker
    (t : LeftExtension f g) (H : IsKan t) {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h] :
    IsKan (t.whisker h) :=
  IsKan.whiskerOfCommute (lanLeftExtension f g) t (IsKan.uniqueUpToIso (lanIsKan f g) H) h
    (isKan f g h)

/--
Definition of `lanCompIsoWhisker` / `lanCompIsoWhisker` 的定义

English:
definition lanCompIsoWhisker
  signature: : lanLeftExtension f (g ≫ h) ≅ (lanLeftExtension f g).whisker h
  body: IsKan.uniqueUpToIso (lanIsKan f (g ≫ h)) (Lan.CommuteWith.isKan f g h)

@[simp]

中文:
定义 lanCompIsoWhisker
  签名: : lanLeftExtension f (g ≫ h) ≅ (lanLeftExtension f g).whisker h
  定义体: IsKan.uniqueUpToIso (lanIsKan f (g ≫ h)) (Lan.CommuteWith.isKan f g h)

@[simp]

Depends on / 依赖: CommuteWith, IsKan.uniqueUpToIso, Lan.CommuteWith.isKan, lanIsKan, preservesColimits_of_createsColimits_and_hasColimits, uniqueUpToIso
-/
def lanCompIsoWhisker : lanLeftExtension f (g ≫ h) ≅ (lanLeftExtension f g).whisker h :=
  IsKan.uniqueUpToIso (lanIsKan f (g ≫ h)) (Lan.CommuteWith.isKan f g h)

@[simp]
/--
theorem `lanCompIsoWhisker_hom_right` / 定理 `lanCompIsoWhisker_hom_right`

English:
theorem lanCompIsoWhisker_hom_right
  proof: rfl

@[simp]

中文:
定理 lanCompIsoWhisker_hom_right
  证明: rfl

@[simp]
-/
theorem lanCompIsoWhisker_hom_right :
    (lanCompIsoWhisker f g h).hom.right = lanDesc ((lanLeftExtension f g).whisker h) :=
  rfl

@[simp]
/--
theorem `lanCompIsoWhisker_inv_right` / 定理 `lanCompIsoWhisker_inv_right`

English:
theorem lanCompIsoWhisker_inv_right
  proof: rfl

中文:
定理 lanCompIsoWhisker_inv_right
  证明: rfl
-/
theorem lanCompIsoWhisker_inv_right :
    (lanCompIsoWhisker f g h).inv.right = (isKan f g h).desc (lanLeftExtension f (g ≫ h)) :=
  rfl

/-- The 1-morphism `h` commutes with the left Kan extension `f⁺ g`. -/
@[simps!]
/--
Definition of `lanCompIso` / `lanCompIso` 的定义

English:
definition lanCompIso
  signature: : f⁺ (g ≫ h) ≅ f⁺ g ≫ h
  body: Comma.rightIso lanCompIsoWhisker f g h

中文:
定义 lanCompIso
  签名: : f⁺ (g ≫ h) ≅ f⁺ g ≫ h
  定义体: Comma.rightIso lanCompIsoWhisker f g h

Depends on / 依赖: Comma.rightIso, lanCompIsoWhisker, rightIso
-/
def lanCompIso : f⁺ (g ≫ h) ≅ f⁺ g ≫ h := Comma.rightIso lanCompIsoWhisker f g h

end Lan.CommuteWith

/--
Definition of `HasAbsLeftKanExtension` / `HasAbsLeftKanExtension` 的定义

English:
class HasAbsLeftKanExtension
  parameters: (f : a ⟶ b) (g : a ⟶ c)
  extends: HasLeftKanExtension f g
  axioms and operations (1):
    - commute({x : B} (h : c ⟶ x)) : Lan.CommuteWith f g h

中文:
类 HasAbsLeftKanExtension
  参数: (f : a ⟶ b) (g : a ⟶ c)
  继承: HasLeftKanExtension f g
  公理与运算 (1 个):
    - commute({x : B} (h : c ⟶ x)) : Lan.CommuteWith f g h
-/
class HasAbsLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop extends HasLeftKanExtension f g where
  commute {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasAbsLeftKanExtension
  signature: f g] {x
  body: HasAbsLeftKanExtension.commute h

中文:
实例 [HasAbsLeftKanExtension
  签名: f g] {x
  定义体: HasAbsLeftKanExtension.commute h

Depends on / 依赖: HasAbsLeftKanExtension, HasAbsLeftKanExtension.commute, commute
-/
instance [HasAbsLeftKanExtension f g] {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h :=
  HasAbsLeftKanExtension.commute h

/--
theorem `LeftExtension.IsAbsKan.hasAbsLeftKanExtension` / 定理 `LeftExtension.IsAbsKan.hasAbsLeftKanExtension`

English:
theorem LeftExtension.IsAbsKan.hasAbsLeftKanExtension
  given: {t : LeftExtension f g} (H : IsAbsKan t)
  proof: have : HasLeftKanExtension f g := H.isKan.hasLeftKanExtension
  ⟨fun h => ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanIsKan f g)) h⟩⟩⟩

中文:
定理 LeftExtension.IsAbsKan.hasAbsLeftKanExtension
  条件: {t : LeftExtension f g} (H : IsAbsKan t)
  证明: have : HasLeftKanExtension f g := H.isKan.hasLeftKanExtension
  ⟨fun h => ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanIsKan f g)) h⟩⟩⟩

Depends on / 依赖: H.isKan, H.isKan.hasLeftKanExtension, H.ofIsoAbsKan, HasLeftKanExtension, IsKan.uniqueUpToIso, hasLeftKanExtension, lanIsKan, ofIsoAbsKan, uniqueUpToIso
-/
theorem LeftExtension.IsAbsKan.hasAbsLeftKanExtension {t : LeftExtension f g} (H : IsAbsKan t) :
    HasAbsLeftKanExtension f g :=
  have : HasLeftKanExtension f g := H.isKan.hasLeftKanExtension
  ⟨fun h => ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanIsKan f g)) h⟩⟩⟩

end LeftKan

section LeftLift

open LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/--
Definition of `HasLeftKanLift` / `HasLeftKanLift` 的定义

English:
class HasLeftKanLift
  parameters: (f : b ⟶ a) (g : c ⟶ a)
  (no additional axioms)

中文:
类 HasLeftKanLift
  参数: (f : b ⟶ a) (g : c ⟶ a)
  (无附加公理)
-/
class HasLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop where mk' ::
hasInitial : HasInitial LeftLift f g

/--
theorem `LeftLift.IsKan.hasLeftKanLift` / 定理 `LeftLift.IsKan.hasLeftKanLift`

English:
theorem LeftLift.IsKan.hasLeftKanLift
  given: {t : LeftLift f g} (H : IsKan t)
  statement: HasLeftKanLift f g
  proof: ⟨IsInitial.hasInitial H⟩

中文:
定理 LeftLift.IsKan.hasLeftKanLift
  条件: {t : LeftLift f g} (H : IsKan t)
  结论: HasLeftKanLift f g
  证明: ⟨IsInitial.hasInitial H⟩

Depends on / 依赖: IsInitial, IsInitial.hasInitial, hasInitial
-/
theorem LeftLift.IsKan.hasLeftKanLift {t : LeftLift f g} (H : IsKan t) : HasLeftKanLift f g :=
  ⟨IsInitial.hasInitial H⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLeftKanLift
  signature: f g] : HasInitial LeftLift f g
  body: HasLeftKanLift.hasInitial

中文:
实例 [HasLeftKanLift
  签名: f g] : HasInitial LeftLift f g
  定义体: HasLeftKanLift.hasInitial

Depends on / 依赖: HasLeftKanLift, HasLeftKanLift.hasInitial, hasInitial
-/
instance [HasLeftKanLift f g] : HasInitial LeftLift f g := HasLeftKanLift.hasInitial

/--
Definition of `lanLiftLeftLift` / `lanLiftLeftLift` 的定义

English:
definition lanLiftLeftLift
  signature: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  body: ⊥_ (LeftLift f g)

中文:
定义 lanLiftLeftLift
  签名: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  定义体: ⊥_ (LeftLift f g)

Depends on / 依赖: LeftLift
-/
def lanLiftLeftLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftLift f g :=
  ⊥_ (LeftLift f g)

/--
Definition of `lanLift` / `lanLift` 的定义

English:
definition lanLift
  signature: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  body: (lanLiftLeftLift f g).lift

中文:
定义 lanLift
  签名: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  定义体: (lanLiftLeftLift f g).lift

Depends on / 依赖: lanLiftLeftLift
-/
def lanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : c ⟶ b :=
  (lanLiftLeftLift f g).lift

/-- `f₊ g` is the left Kan lift of `g` along `f`.
```
            b
          ◹ |
   f₊ g / |
      / | f
    / ▽
  c - - - ▷ a
       g
```
-/
scoped infixr:90 "₊ " => lanLift

@[simp]
/--
theorem `lanLiftLeftLift_lift` / 定理 `lanLiftLeftLift_lift`

English:
theorem lanLiftLeftLift_lift
  given: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  proof: rfl

中文:
定理 lanLiftLeftLift_lift
  条件: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  证明: rfl
-/
theorem lanLiftLeftLift_lift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (lanLiftLeftLift f g).lift = f₊ g := rfl

/--
Definition of `lanLiftUnit` / `lanLiftUnit` 的定义

English:
definition lanLiftUnit
  signature: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  body: (lanLiftLeftLift f g).unit

@[simp]

中文:
定义 lanLiftUnit
  签名: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  定义体: (lanLiftLeftLift f g).unit

@[simp]

Depends on / 依赖: lanLiftLeftLift
-/
def lanLiftUnit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : g ⟶ f₊ g ≫ f :=
  (lanLiftLeftLift f g).unit

@[simp]
/--
theorem `lanLiftLeftLift_unit` / 定理 `lanLiftLeftLift_unit`

English:
theorem lanLiftLeftLift_unit
  given: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  proof: rfl

中文:
定理 lanLiftLeftLift_unit
  条件: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  证明: rfl
-/
theorem lanLiftLeftLift_unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (lanLiftLeftLift f g).unit = lanLiftUnit f g := rfl

/--
Definition of `lanLiftIsKan` / `lanLiftIsKan` 的定义

English:
definition lanLiftIsKan
  signature: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  body: initialIsInitial

中文:
定义 lanLiftIsKan
  签名: (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
  定义体: initialIsInitial

Depends on / 依赖: initialIsInitial
-/
def lanLiftIsKan (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLiftLeftLift f g).IsKan :=
  initialIsInitial

variable {f : b ⟶ a} {g : c ⟶ a}

/--
Definition of `lanLiftDesc` / `lanLiftDesc` 的定义

English:
definition lanLiftDesc
  signature: [HasLeftKanLift f g] (s : LeftLift f g)
  body: (lanLiftIsKan f g).desc s

@[reassoc (attr := simp)]

中文:
定义 lanLiftDesc
  签名: [HasLeftKanLift f g] (s : LeftLift f g)
  定义体: (lanLiftIsKan f g).desc s

@[reassoc (attr := simp)]

Depends on / 依赖: lanLiftIsKan
-/
def lanLiftDesc [HasLeftKanLift f g] (s : LeftLift f g) :
    f₊ g ⟶ s.lift :=
  (lanLiftIsKan f g).desc s

@[reassoc (attr := simp)]
/--
theorem `lanLiftUnit_desc` / 定理 `lanLiftUnit_desc`

English:
theorem lanLiftUnit_desc
  given: [HasLeftKanLift f g] (s : LeftLift f g)
  proof: (lanLiftIsKan f g).fac s

@[simp]

中文:
定理 lanLiftUnit_desc
  条件: [HasLeftKanLift f g] (s : LeftLift f g)
  证明: (lanLiftIsKan f g).fac s

@[simp]

Depends on / 依赖: lanLiftIsKan
-/
theorem lanLiftUnit_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    lanLiftUnit f g ≫ lanLiftDesc s ▷ f = s.unit :=
  (lanLiftIsKan f g).fac s

@[simp]
/--
theorem `lanLiftIsKan_desc` / 定理 `lanLiftIsKan_desc`

English:
theorem lanLiftIsKan_desc
  given: [HasLeftKanLift f g] (s : LeftLift f g)
  proof: rfl

中文:
定理 lanLiftIsKan_desc
  条件: [HasLeftKanLift f g] (s : LeftLift f g)
  证明: rfl
-/
theorem lanLiftIsKan_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    (lanLiftIsKan f g).desc s = lanLiftDesc s :=
  rfl

/--
theorem `LanLift.existsUnique` / 定理 `LanLift.existsUnique`

English:
theorem LanLift.existsUnique
  given: [HasLeftKanLift f g] (s : LeftLift f g)
  proof: (lanLiftIsKan f g).existsUnique _

中文:
定理 LanLift.existsUnique
  条件: [HasLeftKanLift f g] (s : LeftLift f g)
  证明: (lanLiftIsKan f g).existsUnique _

Depends on / 依赖: existsUnique, lanLiftIsKan
-/
theorem LanLift.existsUnique [HasLeftKanLift f g] (s : LeftLift f g) :
    exists! τ, lanLiftUnit f g ≫ τ ▷ f = s.unit :=
  (lanLiftIsKan f g).existsUnique _

/--
Definition of `LanLift.CommuteWith` / `LanLift.CommuteWith` 的定义

English:
class LanLift.CommuteWith
  axioms and operations (1):
    - commute : Nonempty IsKan (lanLiftLeftLift f g).whisker h

中文:
类 LanLift.CommuteWith
  公理与运算 (1 个):
    - commute : Nonempty IsKan (lanLiftLeftLift f g).whisker h
-/
class LanLift.CommuteWith
    (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] {x : B} (h : x ⟶ c) : Prop where
commute : Nonempty IsKan (lanLiftLeftLift f g).whisker h

namespace LanLift.CommuteWith

/--
theorem `of_isKan_whisker` / 定理 `of_isKan_whisker`

English:
theorem of_isKan_whisker
  statement: [HasLeftKanLift f g] (t : LeftLift f g) {x : B} (h : x ⟶ c)
  proof: ⟨⟨IsKan.ofIsoKan H i⟩⟩

中文:
定理 of_isKan_whisker
  结论: [HasLeftKanLift f g] (t : LeftLift f g) {x : B} (h : x ⟶ c)
  证明: ⟨⟨IsKan.ofIsoKan H i⟩⟩

Depends on / 依赖: IsKan.ofIsoKan, ofIsoKan
-/
theorem of_isKan_whisker [HasLeftKanLift f g] (t : LeftLift f g) {x : B} (h : x ⟶ c)
    (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLiftLeftLift f g).whisker h) :
    LanLift.CommuteWith f g h :=
  ⟨⟨IsKan.ofIsoKan H i⟩⟩

/--
theorem `of_lanLift_comp_iso` / 定理 `of_lanLift_comp_iso`

English:
theorem of_lanLift_comp_iso
  statement: [HasLeftKanLift f g]
  proof: ⟨⟨(lanLiftIsKan f (h ≫ g)).ofIsoKan StructuredArrow.isoMk i⟩⟩

中文:
定理 of_lanLift_comp_iso
  结论: [HasLeftKanLift f g]
  证明: ⟨⟨(lanLiftIsKan f (h ≫ g)).ofIsoKan StructuredArrow.isoMk i⟩⟩

Depends on / 依赖: StructuredArrow, StructuredArrow.isoMk, lanLiftIsKan, ofIsoKan
-/
theorem of_lanLift_comp_iso [HasLeftKanLift f g]
    {x : B} {h : x ⟶ c} [HasLeftKanLift f (h ≫ g)]
    (i : f₊ (h ≫ g) ≅ h ≫ f₊ g)
    (w : lanLiftUnit f (h ≫ g) ≫ i.hom ▷ f = h ◁ lanLiftUnit f g ≫ (α_ _ _ _).inv) :
    LanLift.CommuteWith f g h :=
⟨⟨(lanLiftIsKan f (h ≫ g)).ofIsoKan StructuredArrow.isoMk i⟩⟩

variable (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
variable {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h]

/--
Definition of `isKan` / `isKan` 的定义

English:
definition isKan
  signature: : IsKan (lanLiftLeftLift f g).whisker h
  body: Classical.choice LanLift.CommuteWith.commute

中文:
定义 isKan
  签名: : IsKan (lanLiftLeftLift f g).whisker h
  定义体: Classical.choice LanLift.CommuteWith.commute

Depends on / 依赖: Classical, Classical.choice, CommuteWith, LanLift, LanLift.CommuteWith.commute, choice, commute
-/
def isKan : IsKan (lanLiftLeftLift f g).whisker h :=
    Classical.choice LanLift.CommuteWith.commute

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLeftKanLift f (h ≫ g)
  body: (LanLift.CommuteWith.isKan f g h).hasLeftKanLift

中文:
实例 :
  签名: HasLeftKanLift f (h ≫ g)
  定义体: (LanLift.CommuteWith.isKan f g h).hasLeftKanLift

Depends on / 依赖: CommuteWith, LanLift, LanLift.CommuteWith.isKan, hasLeftKanLift
-/
instance : HasLeftKanLift f (h ≫ g) := (LanLift.CommuteWith.isKan f g h).hasLeftKanLift

/--
Definition of `isKanWhisker` / `isKanWhisker` 的定义

English:
definition isKanWhisker
  body: IsKan.whiskerOfCommute (lanLiftLeftLift f g) t (IsKan.uniqueUpToIso (lanLiftIsKan f g) H) h
    (isKan f g h)

中文:
定义 isKanWhisker
  定义体: IsKan.whiskerOfCommute (lanLiftLeftLift f g) t (IsKan.uniqueUpToIso (lanLiftIsKan f g) H) h
    (isKan f g h)

Depends on / 依赖: IsKan.uniqueUpToIso, IsKan.whiskerOfCommute, lanLiftIsKan, lanLiftLeftLift, uniqueUpToIso, whiskerOfCommute
-/
def isKanWhisker
    (t : LeftLift f g) (H : IsKan t) {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h] :
    IsKan (t.whisker h) :=
  IsKan.whiskerOfCommute (lanLiftLeftLift f g) t (IsKan.uniqueUpToIso (lanLiftIsKan f g) H) h
    (isKan f g h)

/--
Definition of `lanLiftCompIsoWhisker` / `lanLiftCompIsoWhisker` 的定义

English:
definition lanLiftCompIsoWhisker
  signature: :
  body: IsKan.uniqueUpToIso (lanLiftIsKan f (h ≫ g)) (LanLift.CommuteWith.isKan f g h)

@[simp]

中文:
定义 lanLiftCompIsoWhisker
  签名: :
  定义体: IsKan.uniqueUpToIso (lanLiftIsKan f (h ≫ g)) (LanLift.CommuteWith.isKan f g h)

@[simp]

Depends on / 依赖: CommuteWith, IsKan.uniqueUpToIso, LanLift, LanLift.CommuteWith.isKan, lanLiftIsKan, uniqueUpToIso
-/
def lanLiftCompIsoWhisker :
    lanLiftLeftLift f (h ≫ g) ≅ (lanLiftLeftLift f g).whisker h :=
  IsKan.uniqueUpToIso (lanLiftIsKan f (h ≫ g)) (LanLift.CommuteWith.isKan f g h)

@[simp]
/--
theorem `lanLiftCompIsoWhisker_hom_right` / 定理 `lanLiftCompIsoWhisker_hom_right`

English:
theorem lanLiftCompIsoWhisker_hom_right
  proof: rfl

@[simp]

中文:
定理 lanLiftCompIsoWhisker_hom_right
  证明: rfl

@[simp]
-/
theorem lanLiftCompIsoWhisker_hom_right :
    (lanLiftCompIsoWhisker f g h).hom.right = lanLiftDesc ((lanLiftLeftLift f g).whisker h) :=
  rfl

@[simp]
/--
theorem `lanLiftCompIsoWhisker_inv_right` / 定理 `lanLiftCompIsoWhisker_inv_right`

English:
theorem lanLiftCompIsoWhisker_inv_right
  proof: rfl

中文:
定理 lanLiftCompIsoWhisker_inv_right
  证明: rfl
-/
theorem lanLiftCompIsoWhisker_inv_right :
    (lanLiftCompIsoWhisker f g h).inv.right = (isKan f g h).desc (lanLiftLeftLift f (h ≫ g)) :=
  rfl

/-- The 1-morphism `h` commutes with the left Kan lift `f₊ g`. -/
@[simps!]
/--
Definition of `lanLiftCompIso` / `lanLiftCompIso` 的定义

English:
definition lanLiftCompIso
  signature: : f₊ (h ≫ g) ≅ h ≫ f₊ g
  body: Comma.rightIso lanLiftCompIsoWhisker f g h

中文:
定义 lanLiftCompIso
  签名: : f₊ (h ≫ g) ≅ h ≫ f₊ g
  定义体: Comma.rightIso lanLiftCompIsoWhisker f g h

Depends on / 依赖: Comma.rightIso, lanLiftCompIsoWhisker, rightIso
-/
def lanLiftCompIso : f₊ (h ≫ g) ≅ h ≫ f₊ g := Comma.rightIso lanLiftCompIsoWhisker f g h

end LanLift.CommuteWith

/--
Definition of `HasAbsLeftKanLift` / `HasAbsLeftKanLift` 的定义

English:
class HasAbsLeftKanLift
  parameters: (f : b ⟶ a) (g : c ⟶ a)
  extends: HasLeftKanLift f g
  axioms and operations (1):
    - commute : forall {x : B} (h : x ⟶ c), LanLift.CommuteWith f g h

中文:
类 HasAbsLeftKanLift
  参数: (f : b ⟶ a) (g : c ⟶ a)
  继承: HasLeftKanLift f g
  公理与运算 (1 个):
    - commute : 对任意 {x : B} (h : x ⟶ c), LanLift.CommuteWith f g h
-/
class HasAbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop extends HasLeftKanLift f g where
  commute : forall {x : B} (h : x ⟶ c), LanLift.CommuteWith f g h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasAbsLeftKanLift
  signature: f g] {x
  body: HasAbsLeftKanLift.commute h

中文:
实例 [HasAbsLeftKanLift
  签名: f g] {x
  定义体: HasAbsLeftKanLift.commute h

Depends on / 依赖: HasAbsLeftKanLift, HasAbsLeftKanLift.commute, commute
-/
instance [HasAbsLeftKanLift f g] {x : B} (h : x ⟶ c) : LanLift.CommuteWith f g h :=
  HasAbsLeftKanLift.commute h

/--
theorem `LeftLift.IsAbsKan.hasAbsLeftKanLift` / 定理 `LeftLift.IsAbsKan.hasAbsLeftKanLift`

English:
theorem LeftLift.IsAbsKan.hasAbsLeftKanLift
  given: {t : LeftLift f g} (H : IsAbsKan t)
  proof: have : HasLeftKanLift f g := H.isKan.hasLeftKanLift
  ⟨fun h => ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanLiftIsKan f g)) h⟩⟩⟩

中文:
定理 LeftLift.IsAbsKan.hasAbsLeftKanLift
  条件: {t : LeftLift f g} (H : IsAbsKan t)
  证明: have : HasLeftKanLift f g := H.isKan.hasLeftKanLift
  ⟨fun h => ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanLiftIsKan f g)) h⟩⟩⟩

Depends on / 依赖: H.isKan, H.isKan.hasLeftKanLift, H.ofIsoAbsKan, HasLeftKanLift, IsKan.uniqueUpToIso, hasLeftKanLift, lanLiftIsKan, ofIsoAbsKan, uniqueUpToIso
-/
theorem LeftLift.IsAbsKan.hasAbsLeftKanLift {t : LeftLift f g} (H : IsAbsKan t) :
    HasAbsLeftKanLift f g :=
  have : HasLeftKanLift f g := H.isKan.hasLeftKanLift
  ⟨fun h => ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanLiftIsKan f g)) h⟩⟩⟩

end LeftLift

end Bicategory

end CategoryTheory
