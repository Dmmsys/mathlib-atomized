/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

In this file, we give the following definitions.
* `RegularMono f`, which is a structure carrying the data that exhibits `f` as a regular
  monomorphism. That is, it carries a fork and data specifying `f` as the equalizer of that fork.
* `IsRegularMono f`, which is a `Prop`-valued class stating that `f` is a regular monomorphism. In
  particular, this doesn't carry any data.

and constructions
* `IsSplitMono f → RegularMono f` and
* `RegularMono f → Mono f`

as well as the dual definitions/constructions for regular epimorphisms.

Additionally, we give the constructions
* `RegularEpi f → EffectiveEpi f`, from which it can be deduced that regular epimorphisms are
  strong.
* `regularEpiOfEffectiveEpi`: constructs a `RegularEpi f` instance from `EffectiveEpi f` and
  `HasPullback f f`.

We also define classes `IsRegularMonoCategory` and `IsRegularEpiCategory` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`StrongMonoCategory`s resp. `StrongEpiCategory`s.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y : C}

/--
Definition of `RegularMono` / `RegularMono` 的定义

English:
structure RegularMono
  parameters: (f : X ⟶ Y)
  axioms and operations (5):
    - Z : C
    - left : Y ⟶ Z
    - right : Y ⟶ Z
    - w : f ≫ left = f ≫ right  [default: by cat_disch]
    - isLimit : IsLimit (Fork.ofι f w)

中文:
结构 正则单态射
  参数: (f : X ⟶ Y)
  公理与运算 (5 个):
    - Z : C
    - left : Y ⟶ Z
    - right : Y ⟶ Z
    - w : f ≫ left = f ≫ right  [默认: by cat_disch]
    - isLimit : 是极限 (叉.ofι f w)

Depends on / 依赖: cat_disch
-/
structure RegularMono (f : X ⟶ Y) where
  /-- An object in `C` -/
  Z : C
  /-- A map from the codomain of `f` to `Z` -/
  left : Y ⟶ Z
  /-- Another map from the codomain of `f` to `Z` -/
  right : Y ⟶ Z
  /-- `f` equalizes the two maps -/
  w : f ≫ left = f ≫ right := by cat_disch
  /-- `f` is the equalizer of the two maps -/
  isLimit : IsLimit (Fork.ofι f w)

attribute [reassoc] RegularMono.w

/--
lemma `RegularMono.mono` / 引理 `RegularMono.mono`

English:
lemma RegularMono.mono
  given: {f : X ⟶ Y} (h : RegularMono f)
  statement: Mono f
  proof: mono_of_isLimit_fork h.isLimit

中文:
引理 正则单态射.mono
  条件: {f : X ⟶ Y} (h : 正则单态射 f)
  结论: 单态射 f
  证明: mono_of_isLimit_fork h.isLimit

Depends on / 依赖: h.isLimit, isLimit, mono_of_isLimit_fork
-/
lemma RegularMono.mono {f : X ⟶ Y} (h : RegularMono f) : Mono f :=
  mono_of_isLimit_fork h.isLimit

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `RegularMono.ofIso` / `RegularMono.ofIso` 的定义

English:
definition RegularMono.ofIso
  signature: (e : X ≅ Y)
  body: Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s => s.ι ≫ e.inv) (by simp) fun s m w => by simp [← w]

中文:
定义 正则单态射.ofIso
  签名: (e : X ≅ Y)
  定义体: Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s => s.ι ≫ e.inv) (by simp) fun s m w => by simp [← w]
-/
def RegularMono.ofIso (e : X ≅ Y) : RegularMono e.hom where
  Z := Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s => s.ι ≫ e.inv) (by simp) fun s m w => by simp [← w]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `RegularMono.ofArrowIso` / `RegularMono.ofArrowIso` 的定义

English:
definition RegularMono.ofArrowIso
  signature: {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
  body: h.Z
  left := e.inv.right ≫ h.left
  right := e.inv.right ≫ h.right
  w := by simp only [← (Arrow.w_mk_assoc e.inv), h.w]
  isLimit := Fork.isLimitOfIsos _ h.isLimit _
    (Arrow.rightFunc.mapIso e) (Iso.refl _) (Arrow.leftFunc.mapIso e)

中文:
定义 正则单态射.ofArrowIso
  签名: {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
  定义体: h.Z
  left := e.inv.right ≫ h.left
  right := e.inv.right ≫ h.right
  w := by simp only [← (Arrow.w_mk_assoc e.inv), h.w]
  isLimit := Fork.isLimitOfIsos _ h.isLimit _
    (Arrow.rightFunc.mapIso e) (Iso.refl _) (Arrow.leftFunc.mapIso e)
-/
def RegularMono.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (h : RegularMono f) :
    RegularMono g where
  Z := h.Z
  left := e.inv.right ≫ h.left
  right := e.inv.right ≫ h.right
  w := by simp only [← (Arrow.w_mk_assoc e.inv), h.w]
  isLimit := Fork.isLimitOfIsos _ h.isLimit _
    (Arrow.rightFunc.mapIso e) (Iso.refl _) (Arrow.leftFunc.mapIso e)

/--
Definition of `IsRegularMono` / `IsRegularMono` 的定义

English:
class IsRegularMono
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - regularMono : Nonempty (RegularMono f)

中文:
类 是正则单态射
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - regularMono : 非空 (正则单态射 f)
-/
class IsRegularMono {X Y : C} (f : X ⟶ Y) : Prop where
  regularMono : Nonempty (RegularMono f)

variable (C) in
/--
Definition of `MorphismProperty.regularMono` / `MorphismProperty.regularMono` 的定义

English:
definition MorphismProperty.regularMono
  signature: : MorphismProperty C
  body: fun _ _ f => IsRegularMono f

@[simp]

中文:
定义 MorphismProperty.regularMono
  签名: : MorphismProperty C
  定义体: fun _ _ f => IsRegularMono f

@[simp]

Depends on / 依赖: IsRegularMono
-/
def MorphismProperty.regularMono : MorphismProperty C := fun _ _ f => IsRegularMono f

@[simp]
/--
theorem `MorphismProperty.regularMono_iff` / 定理 `MorphismProperty.regularMono_iff`

English:
theorem MorphismProperty.regularMono_iff
  given: (f : X ⟶ Y)
  proof: Iff.rfl

中文:
定理 MorphismProperty.regularMono_iff
  条件: (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem MorphismProperty.regularMono_iff (f : X ⟶ Y) :
    (MorphismProperty.regularMono C) f ↔ IsRegularMono f :=
  Iff.rfl

/--
Instance `MorphismProperty.regularMono.containsIdentities` / 实例 `MorphismProperty.regularMono.containsIdentities`

English:
instance MorphismProperty.regularMono.containsIdentities
  signature: :
  body: ⟨⟨RegularMono.ofIso Iso.refl _⟩⟩

中文:
实例 MorphismProperty.regularMono.containsIdentities
  签名: :
  定义体: ⟨⟨RegularMono.ofIso Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl, RegularMono, RegularMono.ofIso
-/
instance MorphismProperty.regularMono.containsIdentities :
    (MorphismProperty.regularMono C).ContainsIdentities where
id_mem _ := ⟨⟨RegularMono.ofIso Iso.refl _⟩⟩

/--
Instance `MorphismProperty.regularMono.respectsIso` / 实例 `MorphismProperty.regularMono.respectsIso`

English:
instance MorphismProperty.regularMono.respectsIso
  signature: :
  body: RespectsIso.of_respects_arrow_iso _ (fun _ _ e h => ⟨⟨.ofArrowIso e (h := h.regularMono.some)⟩⟩)

中文:
实例 MorphismProperty.regularMono.respectsIso
  签名: :
  定义体: RespectsIso.of_respects_arrow_iso _ (fun _ _ e h => ⟨⟨.ofArrowIso e (h := h.regularMono.some)⟩⟩)

Depends on / 依赖: RespectsIso, RespectsIso.of_respects_arrow_iso, h.regularMono.some, hasCardinalLT_subtype_iSup, ofArrowIso, of_respects_arrow_iso, regularMono
-/
instance MorphismProperty.regularMono.respectsIso :
    (MorphismProperty.regularMono C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h => ⟨⟨.ofArrowIso e (h := h.regularMono.some)⟩⟩)

/--
lemma `isRegularMono_of_regularMono` / 引理 `isRegularMono_of_regularMono`

English:
lemma isRegularMono_of_regularMono
  given: {f : X ⟶ Y} (h : RegularMono f)
  statement: IsRegularMono f
  proof: ⟨⟨h⟩⟩

中文:
引理 isRegularMono_of_regularMono
  条件: {f : X ⟶ Y} (h : 正则单态射 f)
  结论: 是正则单态射 f
  证明: ⟨⟨h⟩⟩

Depends on / 依赖: hasCardinalLT_union
-/
lemma isRegularMono_of_regularMono {f : X ⟶ Y} (h : RegularMono f) : IsRegularMono f := ⟨⟨h⟩⟩

/--
Definition of `IsRegularMono.getStruct` / `IsRegularMono.getStruct` 的定义

English:
definition IsRegularMono.getStruct
  signature: (f : X ⟶ Y) [IsRegularMono f]
  body: IsRegularMono.regularMono.some

中文:
定义 是正则单态射.getStruct
  签名: (f : X ⟶ Y) [是正则单态射 f]
  定义体: IsRegularMono.regularMono.some

Depends on / 依赖: IsRegularMono, IsRegularMono.regularMono.some, regularMono
-/
def IsRegularMono.getStruct (f : X ⟶ Y) [IsRegularMono f] : RegularMono f :=
  IsRegularMono.regularMono.some

/--
Definition of `Fork.IsLimit.regularMono` / `Fork.IsLimit.regularMono` 的定义

English:
definition Fork.IsLimit.regularMono
  signature: {A B : C} {p₁ p₂ : A ⟶ B} {c : Fork p₁ p₂} (h : IsLimit c)
  body: B
  left := p₁
  right := p₂
  isLimit := h.ofIsoLimit c.isoForkOfι
  w := c.condition

中文:
定义 叉.是极限.regularMono
  签名: {A B : C} {p₁ p₂ : A ⟶ B} {c : 叉 p₁ p₂} (h : 是极限 c)
  定义体: B
  left := p₁
  right := p₂
  isLimit := h.ofIsoLimit c.isoForkOfι
  w := c.condition
-/
def Fork.IsLimit.regularMono {A B : C} {p₁ p₂ : A ⟶ B} {c : Fork p₁ p₂} (h : IsLimit c) :
    RegularMono c.ι where
  Z := B
  left := p₁
  right := p₂
  isLimit := h.ofIsoLimit c.isoForkOfι
  w := c.condition

section IsRegularMono

/-!

Given a regular monomorphism `f : X ⟶ Y` (i.e. a morphism satisfying the predicate `IsRegularMono`),
this section gives an equalizer diagram
```
     X
    f|
     v
     Y
left| |right
    v v
     Z
```
The names `Z`, `left`, and `right` all being in the `IsRegularMono` namespace.
-/

variable {X Y : C} (f : X ⟶ Y) [IsRegularMono f]

/--
Definition of `IsRegularMono.Z` / `IsRegularMono.Z` 的定义

English:
definition IsRegularMono.Z
  signature: : C
  body: (IsRegularMono.getStruct f).Z

中文:
定义 是正则单态射.Z
  签名: : C
  定义体: (IsRegularMono.getStruct f).Z

Depends on / 依赖: IsRegularMono, IsRegularMono.getStruct, getStruct
-/
def IsRegularMono.Z : C := (IsRegularMono.getStruct f).Z

/--
Definition of `IsRegularMono.left` / `IsRegularMono.left` 的定义

English:
definition IsRegularMono.left
  signature: : Y ⟶ Z f
  body: (IsRegularMono.getStruct f).left

中文:
定义 是正则单态射.left
  签名: : Y ⟶ Z f
  定义体: (IsRegularMono.getStruct f).left

Depends on / 依赖: IsRegularMono, IsRegularMono.getStruct, getStruct
-/
def IsRegularMono.left : Y ⟶ Z f := (IsRegularMono.getStruct f).left

/--
Definition of `IsRegularMono.right` / `IsRegularMono.right` 的定义

English:
definition IsRegularMono.right
  signature: : Y ⟶ Z f
  body: (IsRegularMono.getStruct f).right

中文:
定义 是正则单态射.right
  签名: : Y ⟶ Z f
  定义体: (IsRegularMono.getStruct f).right

Depends on / 依赖: IsRegularMono, IsRegularMono.getStruct, getStruct
-/
def IsRegularMono.right : Y ⟶ Z f := (IsRegularMono.getStruct f).right

/--
lemma `IsRegularMono.w` / 引理 `IsRegularMono.w`

English:
lemma IsRegularMono.w
  statement: f ≫ left f = f ≫ right f
  proof: (IsRegularMono.getStruct f).w

中文:
引理 是正则单态射.w
  结论: f ≫ left f = f ≫ right f
  证明: (IsRegularMono.getStruct f).w

Depends on / 依赖: IsRegularMono, IsRegularMono.getStruct, getStruct
-/
lemma IsRegularMono.w : f ≫ left f = f ≫ right f := (IsRegularMono.getStruct f).w

/--
Definition of `IsRegularMono.isLimit` / `IsRegularMono.isLimit` 的定义

English:
definition IsRegularMono.isLimit
  signature: : IsLimit Fork.ofι _ (w f)
  body: (IsRegularMono.getStruct f).isLimit

中文:
定义 是正则单态射.isLimit
  签名: : 是极限 叉.ofι _ (w f)
  定义体: (IsRegularMono.getStruct f).isLimit

Depends on / 依赖: IsRegularMono, IsRegularMono.getStruct, getStruct, isLimit
-/
def IsRegularMono.isLimit : IsLimit Fork.ofι _ (w f) := (IsRegularMono.getStruct f).isLimit

/--
Definition of `IsRegularMono.lift` / `IsRegularMono.lift` 的定义

English:
definition IsRegularMono.lift
  signature: {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
  body: Fork.IsLimit.lift (isLimit f) k h

@[reassoc (attr := simp)]

中文:
定义 是正则单态射.lift
  签名: {W : C} (f : X ⟶ Y) [是正则单态射 f] (k : W ⟶ Y)
  定义体: Fork.IsLimit.lift (isLimit f) k h

@[reassoc (attr := simp)]

Depends on / 依赖: Fork.IsLimit.lift, IsLimit, isLimit
-/
def IsRegularMono.lift {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) : W ⟶ X :=
  Fork.IsLimit.lift (isLimit f) k h

@[reassoc (attr := simp)]
/--
lemma `IsRegularMono.fac` / 引理 `IsRegularMono.fac`

English:
lemma IsRegularMono.fac
  statement: {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
  proof: Fork.IsLimit.lift_ι (isLimit f)

中文:
引理 是正则单态射.fac
  结论: {W : C} (f : X ⟶ Y) [是正则单态射 f] (k : W ⟶ Y)
  证明: Fork.IsLimit.lift_ι (isLimit f)

Depends on / 依赖: Fork.IsLimit.lift_, IsLimit, isLimit
-/
lemma IsRegularMono.fac {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) : lift f k h ≫ f = k :=
  Fork.IsLimit.lift_ι (isLimit f)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsRegularMono.uniq` / 引理 `IsRegularMono.uniq`

English:
lemma IsRegularMono.uniq
  statement: {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
  proof: .unique hm by simp Fork.IsLimit.existsUnique (isLimit f) k h

中文:
引理 是正则单态射.uniq
  结论: {W : C} (f : X ⟶ Y) [是正则单态射 f] (k : W ⟶ Y)
  证明: .unique hm by simp Fork.IsLimit.existsUnique (isLimit f) k h

Depends on / 依赖: Fork.IsLimit.existsUnique, IsLimit, existsUnique, isLimit, unique
-/
lemma IsRegularMono.uniq {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) (m : W ⟶ X) (hm : m ≫ f = k) : m = lift f k h :=
.unique hm by simp Fork.IsLimit.existsUnique (isLimit f) k h

end IsRegularMono

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `RegularMono.equalizer` / `RegularMono.equalizer` 的定义

English:
definition RegularMono.equalizer
  signature: (g h : X ⟶ Y) [HasLimit (parallelPair g h)]
  body: Y
  left := g
  right := h
  w := equalizer.condition g h
  isLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w => by
      apply equalizer.hom_ext
      simp [← w]

中文:
定义 正则单态射.equalizer
  签名: (g h : X ⟶ Y) [有极限 (parallelPair g h)]
  定义体: Y
  left := g
  right := h
  w := equalizer.condition g h
  isLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w => by
      apply equalizer.hom_ext
      simp [← w]
-/
def RegularMono.equalizer (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    RegularMono (equalizer.ι g h) where
  Z := Y
  left := g
  right := h
  w := equalizer.condition g h
  isLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w => by
      apply equalizer.hom_ext
      simp [← w]

instance (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    IsRegularMono (equalizer.ι g h) :=
isRegularMono_of_regularMono RegularMono.equalizer g h

/--
Definition of `RegularMono.ofIsSplitMono` / `RegularMono.ofIsSplitMono` 的定义

English:
definition RegularMono.ofIsSplitMono
  signature: (f : X ⟶ Y) [IsSplitMono f]
  body: Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f

中文:
定义 正则单态射.ofIsSplitMono
  签名: (f : X ⟶ Y) [是分裂单态射 f]
  定义体: Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f
-/
def RegularMono.ofIsSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    RegularMono f where
  Z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f

instance (priority := 100) (f : X ⟶ Y) [IsSplitMono f] :
    IsRegularMono f :=
isRegularMono_of_regularMono .ofIsSplitMono f

/--
Definition of `RegularMono.lift'` / `RegularMono.lift'` 的定义

English:
definition RegularMono.lift'
  signature: {W : C} {f : X ⟶ Y} (hf : RegularMono f) (k : W ⟶ Y)
  body: Fork.IsLimit.lift' hf.isLimit _ h

中文:
定义 正则单态射.lift'
  签名: {W : C} {f : X ⟶ Y} (hf : 正则单态射 f) (k : W ⟶ Y)
  定义体: Fork.IsLimit.lift' hf.isLimit _ h

Depends on / 依赖: Fork.IsLimit.lift, IsLimit, hf.isLimit, isLimit
-/
def RegularMono.lift' {W : C} {f : X ⟶ Y} (hf : RegularMono f) (k : W ⟶ Y)
    (h : k ≫ hf.left = k ≫ hf.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' hf.isLimit _ h

/--
Definition of `regularOfIsPullbackSndOfRegular` / `regularOfIsPullbackSndOfRegular` 的定义

English:
definition regularOfIsPullbackSndOfRegular
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: hr.Z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by
    repeat (rw [← Category.assoc, ← eq_whisker comm])
    simp only [Category.assoc, hr.w]
  isLimit := by
    apply Fork.IsLimit.mk' _ _
    intro s
    have l₁ : (Fork.ι s ≫ k) ≫ hr.left = (Fork.ι s ≫ k) ≫ hr.right := by
      rw [Catego

中文:
定义 regularOfIsPullbackSndOfRegular
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: hr.Z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by
    repeat (rw [← Category.assoc, ← eq_whisker comm])
    simp only [Category.assoc, hr.w]
  isLimit := by
    apply Fork.IsLimit.mk' _ _
    intro s
    have l₁ : (Fork.ι s ≫ k) ≫ hr.left = (Fork.ι s ≫ k) ≫ hr.right := by
      rw [Catego

Depends on / 依赖: hr.Z
-/
def regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hr : RegularMono h) (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono g where
  Z := hr.Z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by
    repeat (rw [← Category.assoc, ← eq_whisker comm])
    simp only [Category.assoc, hr.w]
  isLimit := by
    apply Fork.IsLimit.mk' _ _
    intro s
    have l₁ : (Fork.ι s ≫ k) ≫ hr.left = (Fork.ι s ≫ k) ≫ hr.right := by
      rw [Category.assoc]; rw [s.condition]; rw [Category.assoc]
    obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hr.isLimit _ l₁
    obtain ⟨p, _, hp₂⟩ := PullbackCone.IsLimit.lift' t _ _ hl
    refine ⟨p, hp₂, ?_⟩
    intro m w
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm
    apply t.hom_ext
    have := hr.mono
    apply (PullbackCone.mk f g comm).equalizer_ext
    · simp only [PullbackCone.mk_π_app, ← cancel_mono h]
      grind [Fork.ofι, PullbackCone.mk]
    · exact z

/--
Definition of `regularOfIsPullbackFstOfRegular` / `regularOfIsPullbackFstOfRegular` 的定义

English:
definition regularOfIsPullbackFstOfRegular
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: regularOfIsPullbackSndOfRegular hk comm.symm (PullbackCone.flipIsLimit t)

中文:
定义 regularOfIsPullbackFstOfRegular
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: regularOfIsPullbackSndOfRegular hk comm.symm (PullbackCone.flipIsLimit t)

Depends on / 依赖: PullbackCone, PullbackCone.flipIsLimit, comm.symm, flipIsLimit, regularOfIsPullbackSndOfRegular
-/
def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hk : RegularMono k) (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono f :=
  regularOfIsPullbackSndOfRegular hk comm.symm (PullbackCone.flipIsLimit t)

/--
lemma `RegularMono.strongMono` / 引理 `RegularMono.strongMono`

English:
lemma RegularMono.strongMono
  given: {f : X ⟶ Y} (h : RegularMono f)
  statement: StrongMono f
  proof: have := h.mono
  StrongMono.mk' (by
      intro A B z hz u v sq
      have : v ≫ h.left = v ≫ h.right := by
        apply (cancel_epi z).1
        repeat (rw [← Category.assoc, ← eq_whisker sq.w])
        simp only [Category.assoc, RegularMono.w]
      obtain ⟨t, ht⟩ := RegularMono.lift' _ _ this
  

中文:
引理 正则单态射.strongMono
  条件: {f : X ⟶ Y} (h : 正则单态射 f)
  结论: 强单态射 f
  证明: have := h.mono
  StrongMono.mk' (by
      intro A B z hz u v sq
      have : v ≫ h.left = v ≫ h.right := by
        apply (cancel_epi z).1
        repeat (rw [← Category.assoc, ← eq_whisker sq.w])
        simp only [Category.assoc, RegularMono.w]
      obtain ⟨t, ht⟩ := RegularMono.lift' _ _ this
  

Depends on / 依赖: Category, Category.assoc, CommSq, CommSq.HasLift.mk, HasLift, RegularMono, RegularMono.lift, RegularMono.w, StrongMono, StrongMono.mk, cancel_epi, cancel_mono, eq_whisker, h.left, h.mono, h.right, repeat, sq.w
-/
lemma RegularMono.strongMono {f : X ⟶ Y} (h : RegularMono f) : StrongMono f :=
  have := h.mono
  StrongMono.mk' (by
      intro A B z hz u v sq
      have : v ≫ h.left = v ≫ h.right := by
        apply (cancel_epi z).1
        repeat (rw [← Category.assoc, ← eq_whisker sq.w])
        simp only [Category.assoc, RegularMono.w]
      obtain ⟨t, ht⟩ := RegularMono.lift' _ _ this
      refine CommSq.HasLift.mk' ⟨t, (cancel_mono f).1 ?_, ht⟩
      simp only [Category.assoc, ht, sq.w])

instance (priority := 100) (f : X ⟶ Y) [IsRegularMono f] : StrongMono f :=
.strongMono IsRegularMono.getStruct f

/--
theorem `isIso_of_regularMono_of_epi` / 定理 `isIso_of_regularMono_of_epi`

English:
theorem isIso_of_regularMono_of_epi
  given: (f : X ⟶ Y) (h : RegularMono f) [Epi f]
  statement: IsIso f
  proof: have := RegularMono.strongMono h
  isIso_of_epi_of_strongMono _

中文:
定理 isIso_of_regularMono_of_epi
  条件: (f : X ⟶ Y) (h : 正则单态射 f) [满态射 f]
  结论: 是同构 f
  证明: have := RegularMono.strongMono h
  isIso_of_epi_of_strongMono _

Depends on / 依赖: RegularMono, RegularMono.strongMono, isIso_of_epi_of_strongMono, strongMono
-/
theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) (h : RegularMono f) [Epi f] : IsIso f :=
  have := RegularMono.strongMono h
  isIso_of_epi_of_strongMono _

section

variable (C)

/--
Definition of `IsRegularMonoCategory` / `IsRegularMonoCategory` 的定义

English:
class IsRegularMonoCategory
  parameters: : Prop where
  axioms and operations (1):
    - regularMonoOfMono : forall {X Y : C} (f : X ⟶ Y) [Mono f], IsRegularMono f

中文:
类 是正则单态射范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - regularMonoOfMono : 对任意 {X Y : C} (f : X ⟶ Y) [单态射 f], 是正则单态射 f
-/
class IsRegularMonoCategory : Prop where
  /-- Every monomorphism is a regular monomorphism -/
  regularMonoOfMono : forall {X Y : C} (f : X ⟶ Y) [Mono f], IsRegularMono f

end

/--
Definition of `regularMonoOfMono` / `regularMonoOfMono` 的定义

English:
definition regularMonoOfMono
  signature: [IsRegularMonoCategory C] (f : X ⟶ Y) [Mono f]
  body: have := IsRegularMonoCategory.regularMonoOfMono f
  IsRegularMono.getStruct f

中文:
定义 regularMonoOfMono
  签名: [是正则单态射范畴 C] (f : X ⟶ Y) [单态射 f]
  定义体: have := IsRegularMonoCategory.regularMonoOfMono f
  IsRegularMono.getStruct f

Depends on / 依赖: IsRegularMono, IsRegularMono.getStruct, IsRegularMonoCategory, IsRegularMonoCategory.regularMonoOfMono, getStruct, regularMonoOfMono
-/
def regularMonoOfMono [IsRegularMonoCategory C] (f : X ⟶ Y) [Mono f] : RegularMono f :=
  have := IsRegularMonoCategory.regularMonoOfMono f
  IsRegularMono.getStruct f

instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    IsRegularMonoCategory C where
  regularMonoOfMono f _ :=
    haveI := isSplitMono_of_mono f
isRegularMono_of_regularMono RegularMono.ofIsSplitMono f

instance (priority := 100) strongMonoCategory_of_regularMonoCategory [IsRegularMonoCategory C] :
    StrongMonoCategory C where
  strongMono_of_mono f _ :=
RegularMono.strongMono regularMonoOfMono f

/--
Definition of `RegularEpi` / `RegularEpi` 的定义

English:
structure RegularEpi
  parameters: (f : X ⟶ Y)
  axioms and operations (4):
    - W : C
    - (left(right) : W ⟶ X)
    - w : left ≫ f = right ≫ f  [default: by cat_disch]
    - isColimit : IsColimit (Cofork.ofπ f w)

中文:
结构 正则满态射
  参数: (f : X ⟶ Y)
  公理与运算 (4 个):
    - W : C
    - (left(right) : W ⟶ X)
    - w : left ≫ f = right ≫ f  [默认: by cat_disch]
    - isColimit : 是余极限 (余叉.ofπ f w)

Depends on / 依赖: cat_disch
-/
structure RegularEpi (f : X ⟶ Y) where
  /-- An object from `C` -/
  W : C
  /-- Two maps to the domain of `f` -/
  (left right : W ⟶ X)
  /-- `f` coequalizes the two maps -/
  w : left ≫ f = right ≫ f := by cat_disch
  /-- `f` is the coequalizer -/
  isColimit : IsColimit (Cofork.ofπ f w)

attribute [reassoc] RegularEpi.w

/--
lemma `RegularEpi.epi` / 引理 `RegularEpi.epi`

English:
lemma RegularEpi.epi
  given: (f : X ⟶ Y) (h : RegularEpi f)
  statement: Epi f
  proof: epi_of_isColimit_cofork h.isColimit

中文:
引理 正则满态射.epi
  条件: (f : X ⟶ Y) (h : 正则满态射 f)
  结论: 满态射 f
  证明: epi_of_isColimit_cofork h.isColimit

Depends on / 依赖: epi_of_isColimit_cofork, h.isColimit, isColimit
-/
lemma RegularEpi.epi (f : X ⟶ Y) (h : RegularEpi f) : Epi f :=
  epi_of_isColimit_cofork h.isColimit

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `RegularEpi.ofIso` / `RegularEpi.ofIso` 的定义

English:
definition RegularEpi.ofIso
  signature: (e : X ≅ Y)
  body: X
  left := 𝟙 X
  right := 𝟙 X
  isColimit := Cofork.IsColimit.mk _ (fun s => e.inv ≫ s.π) (by simp) fun s m w => by
    simp [← w]

中文:
定义 正则满态射.ofIso
  签名: (e : X ≅ Y)
  定义体: X
  left := 𝟙 X
  right := 𝟙 X
  isColimit := Cofork.IsColimit.mk _ (fun s => e.inv ≫ s.π) (by simp) fun s m w => by
    simp [← w]
-/
def RegularEpi.ofIso (e : X ≅ Y) : RegularEpi e.hom where
  W := X
  left := 𝟙 X
  right := 𝟙 X
  isColimit := Cofork.IsColimit.mk _ (fun s => e.inv ≫ s.π) (by simp) fun s m w => by
    simp [← w]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `RegularEpi.ofArrowIso` / `RegularEpi.ofArrowIso` 的定义

English:
definition RegularEpi.ofArrowIso
  signature: {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
  body: h.W
  left := h.left ≫ e.hom.left
  right := h.right ≫ e.hom.left
  w := by
    simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_hom]
    rw [reassoc_of% h.w]
  isColimit := Cofork.isColimitOfIsos _ h.isColimit _
    (Iso.refl _) (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)

中文:
定义 正则满态射.ofArrowIso
  签名: {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
  定义体: h.W
  left := h.left ≫ e.hom.left
  right := h.right ≫ e.hom.left
  w := by
    simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_hom]
    rw [reassoc_of% h.w]
  isColimit := Cofork.isColimitOfIsos _ h.isColimit _
    (Iso.refl _) (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
-/
def RegularEpi.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (h : RegularEpi f) :
    RegularEpi g where
  W := h.W
  left := h.left ≫ e.hom.left
  right := h.right ≫ e.hom.left
  w := by
    simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_hom]
    rw [reassoc_of% h.w]
  isColimit := Cofork.isColimitOfIsos _ h.isColimit _
    (Iso.refl _) (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)

/--
Definition of `IsRegularEpi` / `IsRegularEpi` 的定义

English:
class IsRegularEpi
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - regularEpi : Nonempty (RegularEpi f)

中文:
类 是正则满态射
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - regularEpi : 非空 (正则满态射 f)
-/
class IsRegularEpi {X Y : C} (f : X ⟶ Y) : Prop where
  regularEpi : Nonempty (RegularEpi f)

variable (C) in
/--
Definition of `MorphismProperty.regularEpi` / `MorphismProperty.regularEpi` 的定义

English:
definition MorphismProperty.regularEpi
  signature: : MorphismProperty C
  body: fun _ _ f => IsRegularEpi f

@[simp]

中文:
定义 MorphismProperty.regularEpi
  签名: : MorphismProperty C
  定义体: fun _ _ f => IsRegularEpi f

@[simp]

Depends on / 依赖: IsRegularEpi
-/
def MorphismProperty.regularEpi : MorphismProperty C := fun _ _ f => IsRegularEpi f

@[simp]
/--
theorem `MorphismProperty.regularEpi_iff` / 定理 `MorphismProperty.regularEpi_iff`

English:
theorem MorphismProperty.regularEpi_iff
  given: (f : X ⟶ Y)
  proof: Iff.rfl

中文:
定理 MorphismProperty.regularEpi_iff
  条件: (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem MorphismProperty.regularEpi_iff (f : X ⟶ Y) :
    (MorphismProperty.regularEpi C) f ↔ IsRegularEpi f :=
  Iff.rfl

/--
Instance `MorphismProperty.regularEpi.containsIdentities` / 实例 `MorphismProperty.regularEpi.containsIdentities`

English:
instance MorphismProperty.regularEpi.containsIdentities
  signature: :
  body: ⟨⟨RegularEpi.ofIso Iso.refl _⟩⟩

中文:
实例 MorphismProperty.regularEpi.containsIdentities
  签名: :
  定义体: ⟨⟨RegularEpi.ofIso Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl, RegularEpi, RegularEpi.ofIso
-/
instance MorphismProperty.regularEpi.containsIdentities :
    (MorphismProperty.regularEpi C).ContainsIdentities where
id_mem _ := ⟨⟨RegularEpi.ofIso Iso.refl _⟩⟩

/--
Instance `MorphismProperty.regularEpi.respectsIso` / 实例 `MorphismProperty.regularEpi.respectsIso`

English:
instance MorphismProperty.regularEpi.respectsIso
  signature: :
  body: RespectsIso.of_respects_arrow_iso _ (fun _ _ e h => ⟨⟨.ofArrowIso e (h := h.regularEpi.some)⟩⟩)

中文:
实例 MorphismProperty.regularEpi.respectsIso
  签名: :
  定义体: RespectsIso.of_respects_arrow_iso _ (fun _ _ e h => ⟨⟨.ofArrowIso e (h := h.regularEpi.some)⟩⟩)

Depends on / 依赖: RespectsIso, RespectsIso.of_respects_arrow_iso, h.regularEpi.some, ofArrowIso, of_respects_arrow_iso, regularEpi
-/
instance MorphismProperty.regularEpi.respectsIso :
    (MorphismProperty.regularEpi C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h => ⟨⟨.ofArrowIso e (h := h.regularEpi.some)⟩⟩)

/--
lemma `isRegularEpi_of_regularEpi` / 引理 `isRegularEpi_of_regularEpi`

English:
lemma isRegularEpi_of_regularEpi
  given: {f : X ⟶ Y} (h : RegularEpi f)
  statement: IsRegularEpi f
  proof: ⟨⟨h⟩⟩

中文:
引理 isRegularEpi_of_regularEpi
  条件: {f : X ⟶ Y} (h : 正则满态射 f)
  结论: 是正则满态射 f
  证明: ⟨⟨h⟩⟩
-/
lemma isRegularEpi_of_regularEpi {f : X ⟶ Y} (h : RegularEpi f) : IsRegularEpi f := ⟨⟨h⟩⟩

/--
Definition of `IsRegularEpi.getStruct` / `IsRegularEpi.getStruct` 的定义

English:
definition IsRegularEpi.getStruct
  signature: (f : X ⟶ Y) [h : IsRegularEpi f]
  body: h.regularEpi.some

中文:
定义 是正则满态射.getStruct
  签名: (f : X ⟶ Y) [h : 是正则满态射 f]
  定义体: h.regularEpi.some

Depends on / 依赖: h.regularEpi.some, regularEpi
-/
def IsRegularEpi.getStruct (f : X ⟶ Y) [h : IsRegularEpi f] : RegularEpi f :=
  h.regularEpi.some

/--
Definition of `Cofork.IsColimit.regularEpi` / `Cofork.IsColimit.regularEpi` 的定义

English:
definition Cofork.IsColimit.regularEpi
  signature: {A B : C} {p₁ p₂ : A ⟶ B} {c : Cofork p₁ p₂} (h : IsColimit c)
  body: A
  left := p₁
  right := p₂
  isColimit := h.ofIsoColimit c.isoCoforkOfπ
  w := c.condition

中文:
定义 余叉.是余极限.regularEpi
  签名: {A B : C} {p₁ p₂ : A ⟶ B} {c : 余叉 p₁ p₂} (h : 是余极限 c)
  定义体: A
  left := p₁
  right := p₂
  isColimit := h.ofIsoColimit c.isoCoforkOfπ
  w := c.condition
-/
def Cofork.IsColimit.regularEpi {A B : C} {p₁ p₂ : A ⟶ B} {c : Cofork p₁ p₂} (h : IsColimit c) :
    RegularEpi c.π where
  W := A
  left := p₁
  right := p₂
  isColimit := h.ofIsoColimit c.isoCoforkOfπ
  w := c.condition

section IsRegularEpi

/-!

Given a regular epimorphism `f : X ⟶ Y` (i.e. a morphism satisfying the predicate `IsRegularEpi`),
this section gives a coequalizer diagram
```
     W
left| |right
    v v
     X
    f|
     v
     Y
```
The names `W`, `left`, and `right` all being in the `IsRegularEpi` namespace.
-/

variable {X Y : C} (f : X ⟶ Y) [IsRegularEpi f]

/--
Definition of `IsRegularEpi.W` / `IsRegularEpi.W` 的定义

English:
definition IsRegularEpi.W
  signature: : C
  body: (IsRegularEpi.getStruct f).W

中文:
定义 是正则满态射.W
  签名: : C
  定义体: (IsRegularEpi.getStruct f).W

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, getStruct
-/
def IsRegularEpi.W : C := (IsRegularEpi.getStruct f).W

/--
Definition of `IsRegularEpi.left` / `IsRegularEpi.left` 的定义

English:
definition IsRegularEpi.left
  signature: : W f ⟶ X
  body: (IsRegularEpi.getStruct f).left

中文:
定义 是正则满态射.left
  签名: : W f ⟶ X
  定义体: (IsRegularEpi.getStruct f).left

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, getStruct
-/
def IsRegularEpi.left : W f ⟶ X := (IsRegularEpi.getStruct f).left

/--
Definition of `IsRegularEpi.right` / `IsRegularEpi.right` 的定义

English:
definition IsRegularEpi.right
  signature: : W f ⟶ X
  body: (IsRegularEpi.getStruct f).right

中文:
定义 是正则满态射.right
  签名: : W f ⟶ X
  定义体: (IsRegularEpi.getStruct f).right

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, getStruct
-/
def IsRegularEpi.right : W f ⟶ X := (IsRegularEpi.getStruct f).right

/--
lemma `IsRegularEpi.w` / 引理 `IsRegularEpi.w`

English:
lemma IsRegularEpi.w
  statement: left f ≫ f = right f ≫ f
  proof: (IsRegularEpi.getStruct f).w

中文:
引理 是正则满态射.w
  结论: left f ≫ f = right f ≫ f
  证明: (IsRegularEpi.getStruct f).w

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, getStruct
-/
lemma IsRegularEpi.w : left f ≫ f = right f ≫ f := (IsRegularEpi.getStruct f).w

/--
Definition of `IsRegularEpi.isColimit` / `IsRegularEpi.isColimit` 的定义

English:
definition IsRegularEpi.isColimit
  signature: : IsColimit Cofork.ofπ _ (w f)
  body: (IsRegularEpi.getStruct f).isColimit

中文:
定义 是正则满态射.isColimit
  签名: : 是余极限 余叉.ofπ _ (w f)
  定义体: (IsRegularEpi.getStruct f).isColimit

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, getStruct, isColimit
-/
def IsRegularEpi.isColimit : IsColimit Cofork.ofπ _ (w f) := (IsRegularEpi.getStruct f).isColimit

/--
Definition of `IsRegularEpi.desc` / `IsRegularEpi.desc` 的定义

English:
definition IsRegularEpi.desc
  signature: {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
  body: Cofork.IsColimit.desc (isColimit f) k h

@[reassoc (attr := simp)]

中文:
定义 是正则满态射.desc
  签名: {Z : C} (f : X ⟶ Y) [是正则满态射 f] (k : X ⟶ Z)
  定义体: Cofork.IsColimit.desc (isColimit f) k h

@[reassoc (attr := simp)]

Depends on / 依赖: Cofork, Cofork.IsColimit.desc, IsColimit, isColimit
-/
def IsRegularEpi.desc {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
    (h : left f ≫ k = right f ≫ k) : Y ⟶ Z :=
  Cofork.IsColimit.desc (isColimit f) k h

@[reassoc (attr := simp)]
/--
lemma `IsRegularEpi.fac` / 引理 `IsRegularEpi.fac`

English:
lemma IsRegularEpi.fac
  statement: {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
  proof: Cofork.IsColimit.π_desc (isColimit f)

中文:
引理 是正则满态射.fac
  结论: {Z : C} (f : X ⟶ Y) [是正则满态射 f] (k : X ⟶ Z)
  证明: Cofork.IsColimit.π_desc (isColimit f)

Depends on / 依赖: Cofork, Cofork.IsColimit, IsColimit, isColimit
-/
lemma IsRegularEpi.fac {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
    (h : left f ≫ k = right f ≫ k) : f ≫ desc f k h = k :=
  Cofork.IsColimit.π_desc (isColimit f)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsRegularEpi.uniq` / 引理 `IsRegularEpi.uniq`

English:
lemma IsRegularEpi.uniq
  statement: {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
  proof: .unique hm by simp Cofork.IsColimit.existsUnique (isColimit f) k h

中文:
引理 是正则满态射.uniq
  结论: {Z : C} (f : X ⟶ Y) [是正则满态射 f] (k : X ⟶ Z)
  证明: .unique hm by simp Cofork.IsColimit.existsUnique (isColimit f) k h

Depends on / 依赖: Cofork, Cofork.IsColimit.existsUnique, IsColimit, existsUnique, isColimit, unique
-/
lemma IsRegularEpi.uniq {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
    (h : left f ≫ k = right f ≫ k) (m : Y ⟶ Z) (hm : f ≫ m = k) : m = desc f k h :=
.unique hm by simp Cofork.IsColimit.existsUnique (isColimit f) k h

end IsRegularEpi

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coequalizerRegular` / `coequalizerRegular` 的定义

English:
definition coequalizerRegular
  signature: (g h : X ⟶ Y) [HasColimit (parallelPair g h)]
  body: X
  left := g
  right := h
  w := coequalizer.condition g h
  isColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s) (by simp) fun s m w => by
      apply coequalizer.hom_ext
      simp [← w]

中文:
定义 coequalizerRegular
  签名: (g h : X ⟶ Y) [有余极限 (parallelPair g h)]
  定义体: X
  left := g
  right := h
  w := coequalizer.condition g h
  isColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s) (by simp) fun s m w => by
      apply coequalizer.hom_ext
      simp [← w]
-/
def coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
    RegularEpi (coequalizer.π g h) where
  W := X
  left := g
  right := h
  w := coequalizer.condition g h
  isColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s) (by simp) fun s m w => by
      apply coequalizer.hom_ext
      simp [← w]

instance (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
    IsRegularEpi (coequalizer.π g h) :=
  ⟨⟨coequalizerRegular g h⟩⟩

/--
Definition of `regularEpiOfKernelPair` / `regularEpiOfKernelPair` 的定义

English:
definition regularEpiOfKernelPair
  signature: {B X : C} (f : X ⟶ B) [HasPullback f f]
  body: pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := hc

中文:
定义 regularEpiOfKernelPair
  签名: {B X : C} (f : X ⟶ B) [HasPullback f f]
  定义体: pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := hc

Depends on / 依赖: pullback
-/
def regularEpiOfKernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := hc

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsRegularEpi.of_epi_of_exists` / 引理 `IsRegularEpi.of_epi_of_exists`

English:
lemma IsRegularEpi.of_epi_of_exists
  statement: {X B : C} {f : X ⟶ B} [HasPullback f f] [Epi f]
  proof: by
refine ⟨⟨regularEpiOfKernelPair _ Cofork.IsColimit.mk' _ fun s => ?_⟩⟩
  choose g hg using h s.condition
  refine ⟨g, hg, fun hm => ?_⟩
  rwa [← cancel_epi f, hg]

中文:
引理 是正则满态射.of_epi_of_存在
  结论: {X B : C} {f : X ⟶ B} [HasPullback f f] [满态射 f]
  证明: by
refine ⟨⟨regularEpiOfKernelPair _ Cofork.IsColimit.mk' _ fun s => ?_⟩⟩
  choose g hg using h s.condition
  refine ⟨g, hg, fun hm => ?_⟩
  rwa [← cancel_epi f, hg]

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit, cancel_epi, condition, regularEpiOfKernelPair, s.condition
-/
lemma IsRegularEpi.of_epi_of_exists {X B : C} {f : X ⟶ B} [HasPullback f f] [Epi f]
    (h : forall ⦃Z : C⦄ ⦃g : X ⟶ Z⦄, pullback.fst f f ≫ g = pullback.snd f f ≫ g ->
      exists (u : B ⟶ Z), f ≫ u = g) :
    IsRegularEpi f := by
refine ⟨⟨regularEpiOfKernelPair _ Cofork.IsColimit.mk' _ fun s => ?_⟩⟩
  choose g hg using h s.condition
  refine ⟨g, hg, fun hm => ?_⟩
  rwa [← cancel_epi f, hg]

/--
Definition of `effectiveEpiStructOfRegularEpi` / `effectiveEpiStructOfRegularEpi` 的定义

English:
definition effectiveEpiStructOfRegularEpi
  signature: {B X : C} {f : X ⟶ B} (hf : RegularEpi f)
  body: Cofork.IsColimit.desc hf.isColimit _ (h _ _ hf.w)
  fac _ _ := Cofork.IsColimit.π_desc' hf.isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext hf.isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)

中文:
定义 effectiveEpiStructOfRegularEpi
  签名: {B X : C} {f : X ⟶ B} (hf : 正则满态射 f)
  定义体: Cofork.IsColimit.desc hf.isColimit _ (h _ _ hf.w)
  fac _ _ := Cofork.IsColimit.π_desc' hf.isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext hf.isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)

Depends on / 依赖: Cofork, Cofork.IsColimit.desc, IsColimit, hX.prop_diag_obj, hX.toLimitPresentation, hf.isColimit, hf.w, isColimit, of_limitPresentation, prop_diag_obj, toLimitPresentation
-/
def effectiveEpiStructOfRegularEpi {B X : C} {f : X ⟶ B} (hf : RegularEpi f) :
    EffectiveEpiStruct f where
  desc _ h := Cofork.IsColimit.desc hf.isColimit _ (h _ _ hf.w)
  fac _ _ := Cofork.IsColimit.π_desc' hf.isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext hf.isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)

/--
lemma `RegularEpi.effectiveEpi` / 引理 `RegularEpi.effectiveEpi`

English:
lemma RegularEpi.effectiveEpi
  given: {B X : C} {f : X ⟶ B} (h : RegularEpi f)
  statement: EffectiveEpi f
  proof: ⟨⟨effectiveEpiStructOfRegularEpi h⟩⟩

中文:
引理 正则满态射.effectiveEpi
  条件: {B X : C} {f : X ⟶ B} (h : 正则满态射 f)
  结论: 有效满态射 f
  证明: ⟨⟨effectiveEpiStructOfRegularEpi h⟩⟩

Depends on / 依赖: effectiveEpiStructOfRegularEpi
-/
lemma RegularEpi.effectiveEpi {B X : C} {f : X ⟶ B} (h : RegularEpi f) : EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfRegularEpi h⟩⟩

instance (priority := 100) {B X : C} {f : X ⟶ B} [h : IsRegularEpi f] : EffectiveEpi f :=
.effectiveEpi IsRegularEpi.getStruct f

/--
theorem `effectiveEpi_of_kernelPair` / 定理 `effectiveEpi_of_kernelPair`

English:
theorem effectiveEpi_of_kernelPair
  statement: {B X : C} (f : X ⟶ B) [HasPullback f f]
  proof: RegularEpi.effectiveEpi regularEpiOfKernelPair f hc

中文:
定理 effectiveEpi_of_kernelPair
  结论: {B X : C} (f : X ⟶ B) [HasPullback f f]
  证明: RegularEpi.effectiveEpi regularEpiOfKernelPair f hc

Depends on / 依赖: RegularEpi, RegularEpi.effectiveEpi, effectiveEpi, regularEpiOfKernelPair
-/
theorem effectiveEpi_of_kernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : EffectiveEpi f :=
RegularEpi.effectiveEpi regularEpiOfKernelPair f hc

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitCoforkOfEffectiveEpi` / `isColimitCoforkOfEffectiveEpi` 的定义

English:
definition isColimitCoforkOfEffectiveEpi
  signature: {B X : C} (f : X ⟶ B) [EffectiveEpi f]
  body: EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg => (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg]; rw [Category.assoc]; rw [← Cofork.app_zero_eq_comp_π_right]
      simp)
  fac s := by
    have := EffectiveEpi.fac f (s.ι.app Walkin

中文:
定义 isColimitCoforkOfEffectiveEpi
  签名: {B X : C} (f : X ⟶ B) [有效满态射 f]
  定义体: EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg => (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg]; rw [Category.assoc]; rw [← Cofork.app_zero_eq_comp_π_right]
      simp)
  fac s := by
    have := EffectiveEpi.fac f (s.ι.app Walkin

Depends on / 依赖: Category, Category.assoc, Cofork, Cofork.app_one_eq_, Cofork.app_zero_eq_comp_, EffectiveEpi, EffectiveEpi.desc, EffectiveEpi.fac, IsLimit, PullbackCone, PullbackCone.IsLimit.lift_snd, WalkingParallelPair, WalkingParallelPair.one, all_goals, lift_snd
-/
def isColimitCoforkOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f]
    (c : PullbackCone f f) (hc : IsLimit c) :
    IsColimit (Cofork.ofπ f c.condition) where
  desc s := EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg => (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg]; rw [Category.assoc]; rw [← Cofork.app_zero_eq_comp_π_right]
      simp)
  fac s := by
    have := EffectiveEpi.fac f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg => (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg]; rw [Category.assoc]; rw [← Cofork.app_zero_eq_comp_π_right]
      simp)
    rintro (_ | _)
    all_goals simp_all
  uniq _ _ h := EffectiveEpi.uniq f _ _ _ (h WalkingParallelPair.one)

/--
Definition of `regularEpiOfEffectiveEpi` / `regularEpiOfEffectiveEpi` 的定义

English:
definition regularEpiOfEffectiveEpi
  signature: {B X : C} (f : X ⟶ B) [HasPullback f f]
  body: pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit _ _)

中文:
定义 regularEpiOfEffectiveEpi
  签名: {B X : C} (f : X ⟶ B) [HasPullback f f]
  定义体: pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit _ _)

Depends on / 依赖: pullback
-/
def regularEpiOfEffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit _ _)

/--
Instance `isRegularEpi_of_EffectiveEpi` / 实例 `isRegularEpi_of_EffectiveEpi`

English:
instance isRegularEpi_of_EffectiveEpi
  signature: {B X : C} (f : X ⟶ B) [HasPullback f f]
  body: isRegularEpi_of_regularEpi regularEpiOfEffectiveEpi f

中文:
实例 isRegularEpi_of_EffectiveEpi
  签名: {B X : C} (f : X ⟶ B) [HasPullback f f]
  定义体: isRegularEpi_of_regularEpi regularEpiOfEffectiveEpi f

Depends on / 依赖: isRegularEpi_of_regularEpi, regularEpiOfEffectiveEpi
-/
instance isRegularEpi_of_EffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : IsRegularEpi f :=
isRegularEpi_of_regularEpi regularEpiOfEffectiveEpi f

/--
lemma `isRegularEpi_iff_effectiveEpi` / 引理 `isRegularEpi_iff_effectiveEpi`

English:
lemma isRegularEpi_iff_effectiveEpi
  given: {B X : C} (f : X ⟶ B) [HasPullback f f]
  proof: ⟨fun ⟨_⟩ => inferInstance, fun _ => inferInstance⟩

中文:
引理 isRegularEpi_iff_effectiveEpi
  条件: {B X : C} (f : X ⟶ B) [HasPullback f f]
  证明: ⟨fun ⟨_⟩ => inferInstance, fun _ => inferInstance⟩
-/
lemma isRegularEpi_iff_effectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f] :
    IsRegularEpi f ↔ EffectiveEpi f :=
  ⟨fun ⟨_⟩ => inferInstance, fun _ => inferInstance⟩

/--
Definition of `EffectiveEpiStruct.isColimitCoforkOfIsPullback` / `EffectiveEpiStruct.isColimitCoforkOfIsPullback` 的定义

English:
definition EffectiveEpiStruct.isColimitCoforkOfIsPullback
  body: Cofork.IsColimit.mk _ (fun s => hp.desc s.π (fun {T} g₁ g₂ h => by
      obtain ⟨l, rfl, rfl⟩ := sq.exists_lift g₁ g₂ h
      simp [s.condition]))
    (fun s => hp.fac _ _)
    (fun s m hm => hp.uniq _ _ _ hm)

中文:
定义 EffectiveEpiStruct.isColimitCoforkOfIsPullback
  定义体: Cofork.IsColimit.mk _ (fun s => hp.desc s.π (fun {T} g₁ g₂ h => by
      obtain ⟨l, rfl, rfl⟩ := sq.exists_lift g₁ g₂ h
      simp [s.condition]))
    (fun s => hp.fac _ _)
    (fun s m hm => hp.uniq _ _ _ hm)

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, IsColimit, condition, exists_lift, hp.desc, hp.fac, hp.uniq, s.condition, sq.exists_lift
-/
noncomputable def EffectiveEpiStruct.isColimitCoforkOfIsPullback
    {X Y Z : C} {p : Y ⟶ X} (hp : EffectiveEpiStruct p) {p₁ p₂ : Z ⟶ Y}
    (sq : IsPullback p₁ p₂ p p) :
    IsColimit (Cofork.ofπ p sq.w) :=
  Cofork.IsColimit.mk _ (fun s => hp.desc s.π (fun {T} g₁ g₂ h => by
      obtain ⟨l, rfl, rfl⟩ := sq.exists_lift g₁ g₂ h
      simp [s.condition]))
    (fun s => hp.fac _ _)
    (fun s m hm => hp.uniq _ _ _ hm)

/--
Definition of `RegularEpi.ofSplitEpi` / `RegularEpi.ofSplitEpi` 的定义

English:
definition RegularEpi.ofSplitEpi
  signature: (f : X ⟶ Y) [IsSplitEpi f]
  body: X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f

中文:
定义 正则满态射.ofSplitEpi
  签名: (f : X ⟶ Y) [是分裂满态射 f]
  定义体: X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f

Depends on / 依赖: P.instIsClosedUnderLimitsOfShapeLimitsClosure, instIsClosedUnderLimitsOfShapeLimitsClosure
-/
def RegularEpi.ofSplitEpi (f : X ⟶ Y) [IsSplitEpi f] : RegularEpi f where
  W := X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f

instance (priority := 100) (f : X ⟶ Y) [IsSplitEpi f] : IsRegularEpi f :=
isRegularEpi_of_regularEpi RegularEpi.ofSplitEpi f

/--
Definition of `RegularEpi.desc'` / `RegularEpi.desc'` 的定义

English:
definition RegularEpi.desc'
  signature: {W : C} {f : X ⟶ Y} (hf : RegularEpi f) (k : X ⟶ W)
  body: Cofork.IsColimit.desc' hf.isColimit _ h

中文:
定义 正则满态射.desc'
  签名: {W : C} {f : X ⟶ Y} (hf : 正则满态射 f) (k : X ⟶ W)
  定义体: Cofork.IsColimit.desc' hf.isColimit _ h

Depends on / 依赖: Cofork, Cofork.IsColimit.desc, IsColimit, hf.isColimit, isColimit
-/
def RegularEpi.desc' {W : C} {f : X ⟶ Y} (hf : RegularEpi f) (k : X ⟶ W)
    (h : hf.left ≫ k = hf.right ≫ k) :
    { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' hf.isColimit _ h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `regularOfIsPushoutSndOfRegular` / `regularOfIsPushoutSndOfRegular` 的定义

English:
definition regularOfIsPushoutSndOfRegular
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: gr.W
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by rw [Category.assoc, Category.assoc, comm]; simp only [← Category.assoc, eq_whisker gr.w]
  isColimit := by
    apply Cofork.IsColimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π := by
      rw [← Category.assoc

中文:
定义 regularOfIsPushoutSndOfRegular
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: gr.W
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by rw [Category.assoc, Category.assoc, comm]; simp only [← Category.assoc, eq_whisker gr.w]
  isColimit := by
    apply Cofork.IsColimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π := by
      rw [← Category.assoc

Depends on / 依赖: gr.W
-/
def regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (gr : RegularEpi g) (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi h where
  W := gr.W
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by rw [Category.assoc, Category.assoc, comm]; simp only [← Category.assoc, eq_whisker gr.w]
  isColimit := by
    apply Cofork.IsColimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π := by
      rw [← Category.assoc]; rw [← Category.assoc]; rw [s.condition]
    obtain ⟨l, hl⟩ := Cofork.IsColimit.desc' gr.isColimit (f ≫ Cofork.π s) l₁
    obtain ⟨p, hp₁, _⟩ := PushoutCocone.IsColimit.desc' t _ _ hl.symm
    refine ⟨p, hp₁, ?_⟩
    intro m w
    have z := w.trans hp₁.symm
    apply t.hom_ext
    have := gr.epi
    apply (PushoutCocone.mk _ _ comm).coequalizer_ext
    · exact z
    · erw [← cancel_epi g, ← Category.assoc, ← eq_whisker comm]
      erw [← Category.assoc, ← eq_whisker comm]
      dsimp at z; simp only [Category.assoc, z]

/--
Definition of `regularOfIsPushoutFstOfRegular` / `regularOfIsPushoutFstOfRegular` 的定义

English:
definition regularOfIsPushoutFstOfRegular
  signature: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  body: regularOfIsPushoutSndOfRegular hf comm.symm (PushoutCocone.flipIsColimit t)

中文:
定义 regularOfIsPushoutFstOfRegular
  签名: {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
  定义体: regularOfIsPushoutSndOfRegular hf comm.symm (PushoutCocone.flipIsColimit t)

Depends on / 依赖: PushoutCocone, PushoutCocone.flipIsColimit, comm.symm, flipIsColimit, regularOfIsPushoutSndOfRegular
-/
def regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hf : RegularEpi f) (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi k :=
  regularOfIsPushoutSndOfRegular hf comm.symm (PushoutCocone.flipIsColimit t)

/--
theorem `isIso_of_regularEpi_of_mono` / 定理 `isIso_of_regularEpi_of_mono`

English:
theorem isIso_of_regularEpi_of_mono
  given: (f : X ⟶ Y) (h : RegularEpi f) [Mono f]
  statement: IsIso f
  proof: have := isRegularEpi_of_regularEpi h
  isIso_of_mono_of_strongEpi _

中文:
定理 isIso_of_regularEpi_of_mono
  条件: (f : X ⟶ Y) (h : 正则满态射 f) [单态射 f]
  结论: 是同构 f
  证明: have := isRegularEpi_of_regularEpi h
  isIso_of_mono_of_strongEpi _

Depends on / 依赖: isIso_of_mono_of_strongEpi, isRegularEpi_of_regularEpi
-/
theorem isIso_of_regularEpi_of_mono (f : X ⟶ Y) (h : RegularEpi f) [Mono f] : IsIso f :=
  have := isRegularEpi_of_regularEpi h
  isIso_of_mono_of_strongEpi _

section

/--
Definition of `RegularMono.op` / `RegularMono.op` 的定义

English:
definition RegularMono.op
  signature: {X Y : C} {f : X ⟶ Y} (hf : RegularMono f)
  body: .op hf.Z
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitOp _ _ hf.w _ rfl hf.isLimit

中文:
定义 正则单态射.op
  签名: {X Y : C} {f : X ⟶ Y} (hf : 正则单态射 f)
  定义体: .op hf.Z
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitOp _ _ hf.w _ rfl hf.isLimit

Depends on / 依赖: hf.Z
-/
noncomputable def RegularMono.op {X Y : C} {f : X ⟶ Y} (hf : RegularMono f) :
    RegularEpi f.op where
  W := .op hf.Z
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitOp _ _ hf.w _ rfl hf.isLimit

/--
Definition of `RegularMono.unop` / `RegularMono.unop` 的定义

English:
definition RegularMono.unop
  signature: {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : RegularMono f)
  body: hf.Z.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitUnop _ _ hf.w _ rfl hf.isLimit

中文:
定义 正则单态射.unop
  签名: {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : 正则单态射 f)
  定义体: hf.Z.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitUnop _ _ hf.w _ rfl hf.isLimit

Depends on / 依赖: hf.Z.unop
-/
noncomputable def RegularMono.unop {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : RegularMono f) :
    RegularEpi f.unop where
  W := hf.Z.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitUnop _ _ hf.w _ rfl hf.isLimit

/--
Definition of `RegularEpi.op` / `RegularEpi.op` 的定义

English:
definition RegularEpi.op
  signature: {X Y : C} {f : X ⟶ Y} (hf : RegularEpi f)
  body: .op hf.W
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitOp _ _ hf.w _ rfl hf.isColimit

中文:
定义 正则满态射.op
  签名: {X Y : C} {f : X ⟶ Y} (hf : 正则满态射 f)
  定义体: .op hf.W
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitOp _ _ hf.w _ rfl hf.isColimit

Depends on / 依赖: P.le_strictLimitsClosureIter, hf.W, le_strictLimitsClosureIter
-/
noncomputable def RegularEpi.op {X Y : C} {f : X ⟶ Y} (hf : RegularEpi f) :
    RegularMono f.op where
  Z := .op hf.W
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitOp _ _ hf.w _ rfl hf.isColimit

/--
Definition of `RegularEpi.unop` / `RegularEpi.unop` 的定义

English:
definition RegularEpi.unop
  signature: {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : RegularEpi f)
  body: hf.W.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitUnop _ _ hf.w _ rfl hf.isColimit

@[simp]

中文:
定义 正则满态射.unop
  签名: {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : 正则满态射 f)
  定义体: hf.W.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitUnop _ _ hf.w _ rfl hf.isColimit

@[simp]

Depends on / 依赖: hf.W.unop
-/
noncomputable def RegularEpi.unop {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : RegularEpi f) :
    RegularMono f.unop where
  Z := hf.W.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitUnop _ _ hf.w _ rfl hf.isColimit

@[simp]
/--
lemma `isRegularMono_op_iff_isRegularEpi` / 引理 `isRegularMono_op_iff_isRegularEpi`

English:
lemma isRegularMono_op_iff_isRegularEpi
  given: {X Y : C} (f : X ⟶ Y)
  proof: ⟨fun hf => ⟨⟨hf.regularMono.some.unop⟩⟩, fun hf => ⟨⟨hf.regularEpi.some.op⟩⟩⟩

中文:
引理 isRegularMono_op_iff_isRegularEpi
  条件: {X Y : C} (f : X ⟶ Y)
  证明: ⟨fun hf => ⟨⟨hf.regularMono.some.unop⟩⟩, fun hf => ⟨⟨hf.regularEpi.some.op⟩⟩⟩

Depends on / 依赖: hf.regularEpi.some.op, hf.regularMono.some.unop, regularEpi, regularMono
-/
lemma isRegularMono_op_iff_isRegularEpi {X Y : C} (f : X ⟶ Y) :
    IsRegularMono f.op ↔ IsRegularEpi f :=
  ⟨fun hf => ⟨⟨hf.regularMono.some.unop⟩⟩, fun hf => ⟨⟨hf.regularEpi.some.op⟩⟩⟩

instance {X Y : C} (f : X ⟶ Y) [IsRegularEpi f] : IsRegularMono f.op := by
  simpa

@[simp]
/--
lemma `isRegularMono_unop_iff_isRegularEpi` / 引理 `isRegularMono_unop_iff_isRegularEpi`

English:
lemma isRegularMono_unop_iff_isRegularEpi
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: ⟨fun hf => ⟨⟨hf.regularMono.some.op⟩⟩, fun hf => ⟨⟨hf.regularEpi.some.unop⟩⟩⟩

中文:
引理 isRegularMono_unop_iff_isRegularEpi
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: ⟨fun hf => ⟨⟨hf.regularMono.some.op⟩⟩, fun hf => ⟨⟨hf.regularEpi.some.unop⟩⟩⟩

Depends on / 依赖: hf.regularEpi.some.unop, hf.regularMono.some.op, regularEpi, regularMono
-/
lemma isRegularMono_unop_iff_isRegularEpi {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsRegularMono f.unop ↔ IsRegularEpi f :=
  ⟨fun hf => ⟨⟨hf.regularMono.some.op⟩⟩, fun hf => ⟨⟨hf.regularEpi.some.unop⟩⟩⟩

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsRegularEpi f] : IsRegularMono f.unop := by
  simpa

@[simp]
/--
lemma `isRegularEpi_op_iff_isRegularMono` / 引理 `isRegularEpi_op_iff_isRegularMono`

English:
lemma isRegularEpi_op_iff_isRegularMono
  given: {X Y : C} (f : X ⟶ Y)
  proof: ⟨fun hf => ⟨⟨hf.regularEpi.some.unop⟩⟩, fun hf => ⟨⟨hf.regularMono.some.op⟩⟩⟩

中文:
引理 isRegularEpi_op_iff_isRegularMono
  条件: {X Y : C} (f : X ⟶ Y)
  证明: ⟨fun hf => ⟨⟨hf.regularEpi.some.unop⟩⟩, fun hf => ⟨⟨hf.regularMono.some.op⟩⟩⟩

Depends on / 依赖: hf.regularEpi.some.unop, hf.regularMono.some.op, regularEpi, regularMono
-/
lemma isRegularEpi_op_iff_isRegularMono {X Y : C} (f : X ⟶ Y) :
    IsRegularEpi f.op ↔ IsRegularMono f :=
  ⟨fun hf => ⟨⟨hf.regularEpi.some.unop⟩⟩, fun hf => ⟨⟨hf.regularMono.some.op⟩⟩⟩

instance {X Y : C} (f : X ⟶ Y) [IsRegularMono f] : IsRegularEpi f.op := by
  simpa

@[simp]
/--
lemma `isRegularEpi_unop_iff_isRegularMono` / 引理 `isRegularEpi_unop_iff_isRegularMono`

English:
lemma isRegularEpi_unop_iff_isRegularMono
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: ⟨fun hf => ⟨⟨hf.regularEpi.some.op⟩⟩, fun hf => ⟨⟨hf.regularMono.some.unop⟩⟩⟩

中文:
引理 isRegularEpi_unop_iff_isRegularMono
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: ⟨fun hf => ⟨⟨hf.regularEpi.some.op⟩⟩, fun hf => ⟨⟨hf.regularMono.some.unop⟩⟩⟩

Depends on / 依赖: hf.regularEpi.some.op, hf.regularMono.some.unop, regularEpi, regularMono
-/
lemma isRegularEpi_unop_iff_isRegularMono {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsRegularEpi f.unop ↔ IsRegularMono f :=
  ⟨fun hf => ⟨⟨hf.regularEpi.some.op⟩⟩, fun hf => ⟨⟨hf.regularMono.some.unop⟩⟩⟩

instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsRegularMono f] : IsRegularEpi f.unop := by
  simpa

end

section

variable (C)

/--
Definition of `IsRegularEpiCategory` / `IsRegularEpiCategory` 的定义

English:
class IsRegularEpiCategory
  parameters: : Prop where
  axioms and operations (1):
    - regularEpiOfEpi : forall {X Y : C} (f : X ⟶ Y) [Epi f], IsRegularEpi f

中文:
类 是正则满态射范畴
  参数: : 命题 where
  公理与运算 (1 个):
    - regularEpiOfEpi : 对任意 {X Y : C} (f : X ⟶ Y) [满态射 f], 是正则满态射 f
-/
class IsRegularEpiCategory : Prop where
  /-- Everyone epimorphism is a regular epimorphism -/
  regularEpiOfEpi : forall {X Y : C} (f : X ⟶ Y) [Epi f], IsRegularEpi f

end

/--
Definition of `regularEpiOfEpi` / `regularEpiOfEpi` 的定义

English:
definition regularEpiOfEpi
  signature: [IsRegularEpiCategory C] (f : X ⟶ Y) [Epi f]
  body: have := IsRegularEpiCategory.regularEpiOfEpi f
  IsRegularEpi.getStruct f

中文:
定义 regularEpiOfEpi
  签名: [是正则满态射范畴 C] (f : X ⟶ Y) [满态射 f]
  定义体: have := IsRegularEpiCategory.regularEpiOfEpi f
  IsRegularEpi.getStruct f

Depends on / 依赖: IsRegularEpi, IsRegularEpi.getStruct, IsRegularEpiCategory, IsRegularEpiCategory.regularEpiOfEpi, getStruct, regularEpiOfEpi
-/
def regularEpiOfEpi [IsRegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi f :=
  have := IsRegularEpiCategory.regularEpiOfEpi f
  IsRegularEpi.getStruct f

instance (priority := 100) regularEpiCategoryOfSplitEpiCategory [SplitEpiCategory C] :
    IsRegularEpiCategory C where
  regularEpiOfEpi f _ := by
    have := isSplitEpi_of_epi f
    infer_instance

instance (priority := 100) strongEpiCategory_of_regularEpiCategory [IsRegularEpiCategory C] :
    StrongEpiCategory C where
  strongEpi_of_epi f _ := by
have := isRegularEpi_of_regularEpi regularEpiOfEpi f
    infer_instance

end CategoryTheory
