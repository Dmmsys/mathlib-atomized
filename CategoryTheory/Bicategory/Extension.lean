/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Extensions and lifts in bicategories

We introduce the concept of extensions and lifts within the bicategorical framework. These concepts
are defined by commutative diagrams in the (1-)categorical context. Within the bicategorical
framework, commutative diagrams are replaced by 2-morphisms. Depending on the orientation of the
2-morphisms, we define both left and right extensions (likewise for lifts). The use of left and
right here is a common one in the theory of Kan extensions.

## Implementation notes
We define extensions and lifts as objects in certain comma categories (`StructuredArrow` for left,
and `CostructuredArrow` for right). See the file `CategoryTheory.StructuredArrow` for properties
about these categories. We introduce some intuitive aliases. For example, `LeftExtension.extension`
is an alias for `Comma.right`.

## References
* https://ncatlab.org/nlab/show/lifts+and+extensions
* https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

/--
Definition of `LeftExtension` / `LeftExtension` 的定义

English:
abbreviation LeftExtension
  signature: (f : a ⟶ b) (g : a ⟶ c)
  body: StructuredArrow g (precomp _ f)

中文:
缩写 LeftExtension
  签名: (f : a ⟶ b) (g : a ⟶ c)
  定义体: StructuredArrow g (precomp _ f)

Depends on / 依赖: StructuredArrow, precomp
-/
abbrev LeftExtension (f : a ⟶ b) (g : a ⟶ c) := StructuredArrow g (precomp _ f)

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/--
Definition of `extension` / `extension` 的定义

English:
abbreviation extension
  signature: (t : LeftExtension f g)
  body: t.right

中文:
缩写 extension
  签名: (t : LeftExtension f g)
  定义体: t.right

Depends on / 依赖: t.right
-/
abbrev extension (t : LeftExtension f g) : b ⟶ c := t.right

/--
Definition of `unit` / `unit` 的定义

English:
abbreviation unit
  signature: (t : LeftExtension f g)
  body: t.hom

中文:
缩写 unit
  签名: (t : LeftExtension f g)
  定义体: t.hom

Depends on / 依赖: t.hom
-/
abbrev unit (t : LeftExtension f g) : g ⟶ f ≫ t.extension := t.hom

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (h : b ⟶ c) (unit : g ⟶ f ≫ h)
  body: StructuredArrow.mk unit

中文:
缩写 mk
  签名: (h : b ⟶ c) (unit : g ⟶ f ≫ h)
  定义体: StructuredArrow.mk unit

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
abbrev mk (h : b ⟶ c) (unit : g ⟶ f ≫ h) : LeftExtension f g :=
  StructuredArrow.mk unit

variable {s t : LeftExtension f g}

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by cat_disch)
  body: StructuredArrow.homMk η w

@[reassoc (attr := simp)]

中文:
缩写 homMk
  签名: (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by cat_disch)
  定义体: StructuredArrow.homMk η w

@[reassoc (attr := simp)]

Depends on / 依赖: StructuredArrow, StructuredArrow.homMk, cat_disch
-/
abbrev homMk (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w

@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: (η : s ⟶ t)
  statement: s.unit ≫ f ◁ η.right = t.unit
  proof: StructuredArrow.w η

中文:
定理 w
  条件: (η : s ⟶ t)
  结论: s.unit ≫ f ◁ η.right = t.unit
  证明: StructuredArrow.w η

Depends on / 依赖: StructuredArrow, StructuredArrow.w
-/
theorem w (η : s ⟶ t) : s.unit ≫ f ◁ η.right = t.unit :=
  StructuredArrow.w η

/--
Definition of `alongId` / `alongId` 的定义

English:
definition alongId
  signature: (g : a ⟶ c)
  body: .mk _ (fun_ g).inv

中文:
定义 alongId
  签名: (g : a ⟶ c)
  定义体: .mk _ (fun_ g).inv

Depends on / 依赖: fun_
-/
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g := .mk _ (fun_ g).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LeftExtension (𝟙 a) g)
  body: ⟨alongId g⟩

中文:
实例 :
  签名: 可居 (LeftExtension (𝟙 a) g)
  定义体: ⟨alongId g⟩

Depends on / 依赖: alongId
-/
instance : Inhabited (LeftExtension (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a left extension of `g : a ⟶ c` from a left extension of `g ≫ 𝟙 c`. -/
@[simps!]
/--
Definition of `ofCompId` / `ofCompId` 的定义

English:
definition ofCompId
  signature: (t : LeftExtension f (g ≫ 𝟙 c))
  body: mk (extension t) ((ρ_ g).inv ≫ unit t)

中文:
定义 ofCompId
  签名: (t : LeftExtension f (g ≫ 𝟙 c))
  定义体: mk (extension t) ((ρ_ g).inv ≫ unit t)

Depends on / 依赖: extension
-/
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) : LeftExtension f g :=
  mk (extension t) ((ρ_ g).inv ≫ unit t)

/--
Definition of `whisker` / `whisker` 的定义

English:
definition whisker
  signature: (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  body: .mk _ t.unit ▷ h ≫ (α_ _ _ _).hom

@[simp]

中文:
定义 whisker
  签名: (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  定义体: .mk _ t.unit ▷ h ≫ (α_ _ _ _).hom

@[simp]

Depends on / 依赖: t.unit
-/
def whisker (t : LeftExtension f g) {x : B} (h : c ⟶ x) : LeftExtension f (g ≫ h) :=
.mk _ t.unit ▷ h ≫ (α_ _ _ _).hom

@[simp]
/--
theorem `whisker_extension` / 定理 `whisker_extension`

English:
theorem whisker_extension
  given: (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  proof: rfl

@[simp]

中文:
定理 whisker_extension
  条件: (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  证明: rfl

@[simp]
-/
theorem whisker_extension (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).extension = t.extension ≫ h :=
  rfl

@[simp]
/--
theorem `whisker_unit` / 定理 `whisker_unit`

English:
theorem whisker_unit
  given: (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  proof: rfl

中文:
定理 whisker_unit
  条件: (t : LeftExtension f g) {x : B} (h : c ⟶ x)
  证明: rfl
-/
theorem whisker_unit (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).unit = t.unit ▷ h ≫ (α_ f t.extension h).hom :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: {x : B} (h : c ⟶ x)
  body: t.whisker h
map η := LeftExtension.homMk (η.right ▷ h) by
    simp [-LeftExtension.w, ← LeftExtension.w η]

中文:
定义 whiskering
  签名: {x : B} (h : c ⟶ x)
  定义体: t.whisker h
map η := LeftExtension.homMk (η.right ▷ h) by
    simp [-LeftExtension.w, ← LeftExtension.w η]

Depends on / 依赖: t.whisker, whisker
-/
def whiskering {x : B} (h : c ⟶ x) : LeftExtension f g ⥤ LeftExtension f (g ≫ h) where
  obj t := t.whisker h
map η := LeftExtension.homMk (η.right ▷ h) by
    simp [-LeftExtension.w, ← LeftExtension.w η]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between left extensions by cancelling the whiskered identities. -/
@[simps! right]
/--
Definition of `whiskerIdCancel` / `whiskerIdCancel` 的定义

English:
definition whiskerIdCancel
  body: LeftExtension.homMk (τ.right ≫ (ρ_ _).hom)

中文:
定义 whiskerIdCancel
  定义体: LeftExtension.homMk (τ.right ≫ (ρ_ _).hom)

Depends on / 依赖: LeftExtension, LeftExtension.homMk
-/
def whiskerIdCancel
    (s : LeftExtension f (g ≫ 𝟙 c)) {t : LeftExtension f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofCompId ⟶ t :=
  LeftExtension.homMk (τ.right ≫ (ρ_ _).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered extensions. -/
@[simps! right]
/--
Definition of `whiskerHom` / `whiskerHom` 的定义

English:
definition whiskerHom
  signature: (i : s ⟶ t) {x : B} (h : c ⟶ x)
  body: StructuredArrow.homMk (i.right ▷ h) by
    rw [← cancel_mono (α_ _ _ _).inv]
    calc
      _ = (unit s ≫ f ◁ i.right) ▷ h := by simp [-LeftExtension.w]
      _ = unit t ▷ h := congrArg (· ▷ h) (LeftExtension.w i)
      _ = _ := by simp

中文:
定义 whiskerHom
  签名: (i : s ⟶ t) {x : B} (h : c ⟶ x)
  定义体: StructuredArrow.homMk (i.right ▷ h) by
    rw [← cancel_mono (α_ _ _ _).inv]
    calc
      _ = (unit s ≫ f ◁ i.right) ▷ h := by simp [-LeftExtension.w]
      _ = unit t ▷ h := congrArg (· ▷ h) (LeftExtension.w i)
      _ = _ := by simp

Depends on / 依赖: LeftExtension, LeftExtension.w, StructuredArrow, StructuredArrow.homMk, cancel_mono, i.right
-/
def whiskerHom (i : s ⟶ t) {x : B} (h : c ⟶ x) :
    s.whisker h ⟶ t.whisker h :=
StructuredArrow.homMk (i.right ▷ h) by
    rw [← cancel_mono (α_ _ _ _).inv]
    calc
      _ = (unit s ≫ f ◁ i.right) ▷ h := by simp [-LeftExtension.w]
      _ = unit t ▷ h := congrArg (· ▷ h) (LeftExtension.w i)
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `whiskerIso` / `whiskerIso` 的定义

English:
definition whiskerIso
  signature: (i : s ≅ t) {x : B} (h : c ⟶ x)
  body: Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.hom ≫ i.inv).right ▷ h := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.inv ≫ i.hom).right ▷ h := by s

中文:
定义 whiskerIso
  签名: (i : s ≅ t) {x : B} (h : c ⟶ x)
  定义体: Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.hom ≫ i.inv).right ▷ h := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.inv ≫ i.hom).right ▷ h := by s

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, Iso.mk, StructuredArrow, StructuredArrow.hom_ext, hom_ext, hom_inv_id, i.hom, i.inv, inv_hom_id, whiskerHom
-/
def whiskerIso (i : s ≅ t) {x : B} (h : c ⟶ x) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.hom ≫ i.inv).right ▷ h := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.inv ≫ i.hom).right ▷ h := by simp [-Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between left extensions induced by a right unitor. -/
@[simps! hom_right inv_right]
/--
Definition of `whiskerOfCompIdIsoSelf` / `whiskerOfCompIdIsoSelf` 的定义

English:
definition whiskerOfCompIdIsoSelf
  signature: (t : LeftExtension f g)
  body: StructuredArrow.isoMk (ρ_ (t.extension))

中文:
定义 whiskerOfCompIdIsoSelf
  签名: (t : LeftExtension f g)
  定义体: StructuredArrow.isoMk (ρ_ (t.extension))

Depends on / 依赖: StructuredArrow, StructuredArrow.isoMk, extension, t.extension
-/
def whiskerOfCompIdIsoSelf (t : LeftExtension f g) : (t.whisker (𝟙 c)).ofCompId ≅ t :=
  StructuredArrow.isoMk (ρ_ (t.extension))

end LeftExtension

/--
Definition of `LeftLift` / `LeftLift` 的定义

English:
abbreviation LeftLift
  signature: (f : b ⟶ a) (g : c ⟶ a)
  body: StructuredArrow g (postcomp _ f)

中文:
缩写 LeftLift
  签名: (f : b ⟶ a) (g : c ⟶ a)
  定义体: StructuredArrow g (postcomp _ f)

Depends on / 依赖: StructuredArrow, postcomp
-/
abbrev LeftLift (f : b ⟶ a) (g : c ⟶ a) := StructuredArrow g (postcomp _ f)

namespace LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/--
Definition of `lift` / `lift` 的定义

English:
abbreviation lift
  signature: (t : LeftLift f g)
  body: t.right

中文:
缩写 lift
  签名: (t : LeftLift f g)
  定义体: t.right

Depends on / 依赖: t.right
-/
abbrev lift (t : LeftLift f g) : c ⟶ b := t.right

/--
Definition of `unit` / `unit` 的定义

English:
abbreviation unit
  signature: (t : LeftLift f g)
  body: t.hom

中文:
缩写 unit
  签名: (t : LeftLift f g)
  定义体: t.hom

Depends on / 依赖: t.hom
-/
abbrev unit (t : LeftLift f g) : g ⟶ t.lift ≫ f := t.hom

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (h : c ⟶ b) (unit : g ⟶ h ≫ f)
  body: StructuredArrow.mk unit

中文:
缩写 mk
  签名: (h : c ⟶ b) (unit : g ⟶ h ≫ f)
  定义体: StructuredArrow.mk unit

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
abbrev mk (h : c ⟶ b) (unit : g ⟶ h ≫ f) : LeftLift f g :=
  StructuredArrow.mk unit

variable {s t : LeftLift f g}

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit := by cat_disch)
  body: StructuredArrow.homMk η w

@[reassoc (attr := simp)]

中文:
缩写 homMk
  签名: (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit := by cat_disch)
  定义体: StructuredArrow.homMk η w

@[reassoc (attr := simp)]

Depends on / 依赖: StructuredArrow, StructuredArrow.homMk, cat_disch
-/
abbrev homMk (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w

@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: (h : s ⟶ t)
  statement: s.unit ≫ h.right ▷ f = t.unit
  proof: StructuredArrow.w h

中文:
定理 w
  条件: (h : s ⟶ t)
  结论: s.unit ≫ h.right ▷ f = t.unit
  证明: StructuredArrow.w h

Depends on / 依赖: StructuredArrow, StructuredArrow.w
-/
theorem w (h : s ⟶ t) : s.unit ≫ h.right ▷ f = t.unit :=
  StructuredArrow.w h

/--
Definition of `alongId` / `alongId` 的定义

English:
definition alongId
  signature: (g : c ⟶ a)
  body: .mk _ (ρ_ g).inv

中文:
定义 alongId
  签名: (g : c ⟶ a)
  定义体: .mk _ (ρ_ g).inv
-/
def alongId (g : c ⟶ a) : LeftLift (𝟙 a) g := .mk _ (ρ_ g).inv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LeftLift (𝟙 a) g)
  body: ⟨alongId g⟩

中文:
实例 :
  签名: 可居 (LeftLift (𝟙 a) g)
  定义体: ⟨alongId g⟩

Depends on / 依赖: alongId
-/
instance : Inhabited (LeftLift (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a left lift along `g : c ⟶ a` from a left lift along `𝟙 c ≫ g`. -/
@[simps!]
/--
Definition of `ofIdComp` / `ofIdComp` 的定义

English:
definition ofIdComp
  signature: (t : LeftLift f (𝟙 c ≫ g))
  body: mk (lift t) ((fun_ _).inv ≫ unit t)

中文:
定义 ofIdComp
  签名: (t : LeftLift f (𝟙 c ≫ g))
  定义体: mk (lift t) ((fun_ _).inv ≫ unit t)

Depends on / 依赖: fun_
-/
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) : LeftLift f g :=
  mk (lift t) ((fun_ _).inv ≫ unit t)

/--
Definition of `whisker` / `whisker` 的定义

English:
definition whisker
  signature: (t : LeftLift f g) {x : B} (h : x ⟶ c)
  body: .mk _ h ◁ t.unit ≫ (α_ _ _ _).inv

@[simp]

中文:
定义 whisker
  签名: (t : LeftLift f g) {x : B} (h : x ⟶ c)
  定义体: .mk _ h ◁ t.unit ≫ (α_ _ _ _).inv

@[simp]

Depends on / 依赖: t.unit
-/
def whisker (t : LeftLift f g) {x : B} (h : x ⟶ c) : LeftLift f (h ≫ g) :=
.mk _ h ◁ t.unit ≫ (α_ _ _ _).inv

@[simp]
/--
theorem `whisker_lift` / 定理 `whisker_lift`

English:
theorem whisker_lift
  given: (t : LeftLift f g) {x : B} (h : x ⟶ c)
  proof: rfl

@[simp]

中文:
定理 whisker_lift
  条件: (t : LeftLift f g) {x : B} (h : x ⟶ c)
  证明: rfl

@[simp]
-/
theorem whisker_lift (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).lift = h ≫ t.lift :=
  rfl

@[simp]
/--
theorem `whisker_unit` / 定理 `whisker_unit`

English:
theorem whisker_unit
  given: (t : LeftLift f g) {x : B} (h : x ⟶ c)
  proof: rfl

中文:
定理 whisker_unit
  条件: (t : LeftLift f g) {x : B} (h : x ⟶ c)
  证明: rfl
-/
theorem whisker_unit (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).unit = h ◁ t.unit ≫ (α_ h t.lift f).inv :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: {x : B} (h : x ⟶ c)
  body: t.whisker h
map η := LeftLift.homMk (h ◁ η.right) by
    dsimp only [whisker_lift, whisker_unit]
    rw [← LeftLift.w η]
    simp [-LeftLift.w]

中文:
定义 whiskering
  签名: {x : B} (h : x ⟶ c)
  定义体: t.whisker h
map η := LeftLift.homMk (h ◁ η.right) by
    dsimp only [whisker_lift, whisker_unit]
    rw [← LeftLift.w η]
    simp [-LeftLift.w]

Depends on / 依赖: t.whisker, whisker
-/
def whiskering {x : B} (h : x ⟶ c) : LeftLift f g ⥤ LeftLift f (h ≫ g) where
  obj t := t.whisker h
map η := LeftLift.homMk (h ◁ η.right) by
    dsimp only [whisker_lift, whisker_unit]
    rw [← LeftLift.w η]
    simp [-LeftLift.w]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between left lifts by cancelling the whiskered identities. -/
@[simps! right]
/--
Definition of `whiskerIdCancel` / `whiskerIdCancel` 的定义

English:
definition whiskerIdCancel
  body: LeftLift.homMk (τ.right ≫ (fun_ _).hom)

中文:
定义 whiskerIdCancel
  定义体: LeftLift.homMk (τ.right ≫ (fun_ _).hom)

Depends on / 依赖: LeftLift, LeftLift.homMk, fun_
-/
def whiskerIdCancel
    (s : LeftLift f (𝟙 c ≫ g)) {t : LeftLift f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofIdComp ⟶ t :=
  LeftLift.homMk (τ.right ≫ (fun_ _).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered lifts. -/
@[simps! right]
/--
Definition of `whiskerHom` / `whiskerHom` 的定义

English:
definition whiskerHom
  signature: (i : s ⟶ t) {x : B} (h : x ⟶ c)
  body: StructuredArrow.homMk (h ◁ i.right) by
    rw [← cancel_mono (α_ h _ _).hom]
    calc
      _ = h ◁ (unit s ≫ i.right ▷ f) := by simp [-LeftLift.w]
      _ = h ◁ unit t := congrArg (h ◁ ·) (LeftLift.w i)
      _ = _ := by simp

中文:
定义 whiskerHom
  签名: (i : s ⟶ t) {x : B} (h : x ⟶ c)
  定义体: StructuredArrow.homMk (h ◁ i.right) by
    rw [← cancel_mono (α_ h _ _).hom]
    calc
      _ = h ◁ (unit s ≫ i.right ▷ f) := by simp [-LeftLift.w]
      _ = h ◁ unit t := congrArg (h ◁ ·) (LeftLift.w i)
      _ = _ := by simp

Depends on / 依赖: LeftLift, LeftLift.w, StructuredArrow, StructuredArrow.homMk, cancel_mono, i.right
-/
def whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) :
    s.whisker h ⟶ t.whisker h :=
StructuredArrow.homMk (h ◁ i.right) by
    rw [← cancel_mono (α_ h _ _).hom]
    calc
      _ = h ◁ (unit s ≫ i.right ▷ f) := by simp [-LeftLift.w]
      _ = h ◁ unit t := congrArg (h ◁ ·) (LeftLift.w i)
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `whiskerIso` / `whiskerIso` 的定义

English:
definition whiskerIso
  signature: (i : s ≅ t) {x : B} (h : x ⟶ c)
  body: Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).right := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).right := by s

中文:
定义 whiskerIso
  签名: (i : s ≅ t) {x : B} (h : x ⟶ c)
  定义体: Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).right := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).right := by s

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id, Iso.mk, StructuredArrow, StructuredArrow.hom_ext, hom_ext, hom_inv_id, i.hom, i.inv, inv_hom_id, whiskerHom
-/
def whiskerIso (i : s ≅ t) {x : B} (h : x ⟶ c) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).right := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).right := by simp [-Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between left lifts induced by a left unitor. -/
@[simps! hom_right inv_right]
/--
Definition of `whiskerOfIdCompIsoSelf` / `whiskerOfIdCompIsoSelf` 的定义

English:
definition whiskerOfIdCompIsoSelf
  signature: (t : LeftLift f g)
  body: StructuredArrow.isoMk (fun_ (lift t))

中文:
定义 whiskerOfIdCompIsoSelf
  签名: (t : LeftLift f g)
  定义体: StructuredArrow.isoMk (fun_ (lift t))

Depends on / 依赖: StructuredArrow, StructuredArrow.isoMk, fun_
-/
def whiskerOfIdCompIsoSelf (t : LeftLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  StructuredArrow.isoMk (fun_ (lift t))

end LeftLift

/--
Definition of `RightExtension` / `RightExtension` 的定义

English:
abbreviation RightExtension
  signature: (f : a ⟶ b) (g : a ⟶ c)
  body: CostructuredArrow (precomp _ f) g

中文:
缩写 RightExtension
  签名: (f : a ⟶ b) (g : a ⟶ c)
  定义体: CostructuredArrow (precomp _ f) g

Depends on / 依赖: CostructuredArrow, precomp
-/
abbrev RightExtension (f : a ⟶ b) (g : a ⟶ c) := CostructuredArrow (precomp _ f) g

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/--
Definition of `extension` / `extension` 的定义

English:
abbreviation extension
  signature: (t : RightExtension f g)
  body: t.left

中文:
缩写 extension
  签名: (t : RightExtension f g)
  定义体: t.left

Depends on / 依赖: t.left
-/
abbrev extension (t : RightExtension f g) : b ⟶ c := t.left

/--
Definition of `counit` / `counit` 的定义

English:
abbreviation counit
  signature: (t : RightExtension f g)
  body: t.hom

中文:
缩写 counit
  签名: (t : RightExtension f g)
  定义体: t.hom

Depends on / 依赖: t.hom
-/
abbrev counit (t : RightExtension f g) : f ≫ t.extension ⟶ g := t.hom

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (h : b ⟶ c) (counit : f ≫ h ⟶ g)
  body: CostructuredArrow.mk counit

中文:
缩写 mk
  签名: (h : b ⟶ c) (counit : f ≫ h ⟶ g)
  定义体: CostructuredArrow.mk counit

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, counit
-/
abbrev mk (h : b ⟶ c) (counit : f ≫ h ⟶ g) : RightExtension f g :=
  CostructuredArrow.mk counit

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {s t : RightExtension f g} (η : s.extension ⟶ t.extension)
  body: CostructuredArrow.homMk η w

@[reassoc (attr := simp)]

中文:
缩写 homMk
  签名: {s t : RightExtension f g} (η : s.extension ⟶ t.extension)
  定义体: CostructuredArrow.homMk η w

@[reassoc (attr := simp)]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, cat_disch
-/
abbrev homMk {s t : RightExtension f g} (η : s.extension ⟶ t.extension)
    (w : f ◁ η ≫ t.counit = s.counit := by cat_disch) : s ⟶ t :=
  CostructuredArrow.homMk η w

@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: {s t : RightExtension f g} (η : s ⟶ t)
  proof: CostructuredArrow.w η

中文:
定理 w
  条件: {s t : RightExtension f g} (η : s ⟶ t)
  证明: CostructuredArrow.w η

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w
-/
theorem w {s t : RightExtension f g} (η : s ⟶ t) :
    f ◁ η.left ≫ t.counit = s.counit :=
  CostructuredArrow.w η

/--
Definition of `alongId` / `alongId` 的定义

English:
definition alongId
  signature: (g : a ⟶ c)
  body: .mk _ (fun_ g).hom

中文:
定义 alongId
  签名: (g : a ⟶ c)
  定义体: .mk _ (fun_ g).hom

Depends on / 依赖: fun_
-/
def alongId (g : a ⟶ c) : RightExtension (𝟙 a) g := .mk _ (fun_ g).hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RightExtension (𝟙 a) g)
  body: ⟨alongId g⟩

中文:
实例 :
  签名: 可居 (RightExtension (𝟙 a) g)
  定义体: ⟨alongId g⟩

Depends on / 依赖: alongId
-/
instance : Inhabited (RightExtension (𝟙 a) g) := ⟨alongId g⟩

end RightExtension

/--
Definition of `RightLift` / `RightLift` 的定义

English:
abbreviation RightLift
  signature: (f : b ⟶ a) (g : c ⟶ a)
  body: CostructuredArrow (postcomp _ f) g

中文:
缩写 RightLift
  签名: (f : b ⟶ a) (g : c ⟶ a)
  定义体: CostructuredArrow (postcomp _ f) g

Depends on / 依赖: CostructuredArrow, postcomp
-/
abbrev RightLift (f : b ⟶ a) (g : c ⟶ a) := CostructuredArrow (postcomp _ f) g

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/--
Definition of `lift` / `lift` 的定义

English:
abbreviation lift
  signature: (t : RightLift f g)
  body: t.left

中文:
缩写 lift
  签名: (t : RightLift f g)
  定义体: t.left

Depends on / 依赖: t.left
-/
abbrev lift (t : RightLift f g) : c ⟶ b := t.left

/--
Definition of `counit` / `counit` 的定义

English:
abbreviation counit
  signature: (t : RightLift f g)
  body: t.hom

中文:
缩写 counit
  签名: (t : RightLift f g)
  定义体: t.hom

Depends on / 依赖: t.hom
-/
abbrev counit (t : RightLift f g) : t.lift ≫ f ⟶ g := t.hom

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (h : c ⟶ b) (counit : h ≫ f ⟶ g)
  body: CostructuredArrow.mk counit

中文:
缩写 mk
  签名: (h : c ⟶ b) (counit : h ≫ f ⟶ g)
  定义体: CostructuredArrow.mk counit

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, counit
-/
abbrev mk (h : c ⟶ b) (counit : h ≫ f ⟶ g) : RightLift f g :=
  CostructuredArrow.mk counit

variable {s t : RightLift f g}

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit := by cat_disch)
  body: CostructuredArrow.homMk η w

@[reassoc (attr := simp)]

中文:
缩写 homMk
  签名: (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit := by cat_disch)
  定义体: CostructuredArrow.homMk η w

@[reassoc (attr := simp)]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, cat_disch
-/
abbrev homMk (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit := by cat_disch) :
    s ⟶ t :=
  CostructuredArrow.homMk η w

@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: (h : s ⟶ t)
  statement: h.left ▷ f ≫ t.counit = s.counit
  proof: CostructuredArrow.w h

中文:
定理 w
  条件: (h : s ⟶ t)
  结论: h.left ▷ f ≫ t.counit = s.counit
  证明: CostructuredArrow.w h

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w
-/
theorem w (h : s ⟶ t) : h.left ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.w h

/--
Definition of `alongId` / `alongId` 的定义

English:
definition alongId
  signature: (g : c ⟶ a)
  body: .mk _ (ρ_ g).hom

中文:
定义 alongId
  签名: (g : c ⟶ a)
  定义体: .mk _ (ρ_ g).hom
-/
def alongId (g : c ⟶ a) : RightLift (𝟙 a) g := .mk _ (ρ_ g).hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RightLift (𝟙 a) g)
  body: ⟨alongId g⟩

中文:
实例 :
  签名: 可居 (RightLift (𝟙 a) g)
  定义体: ⟨alongId g⟩

Depends on / 依赖: alongId
-/
instance : Inhabited (RightLift (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a right lift along `g : c ⟶ a` from a right lift along `𝟙 c ≫ g`. -/
@[simps!]
/--
Definition of `ofIdComp` / `ofIdComp` 的定义

English:
definition ofIdComp
  signature: (t : RightLift f (𝟙 c ≫ g))
  body: mk (lift t) (counit t ≫ (fun_ _).hom)

中文:
定义 ofIdComp
  签名: (t : RightLift f (𝟙 c ≫ g))
  定义体: mk (lift t) (counit t ≫ (fun_ _).hom)

Depends on / 依赖: counit, fun_, sq_hasLift_of_hasLiftingProperty
-/
def ofIdComp (t : RightLift f (𝟙 c ≫ g)) : RightLift f g :=
  mk (lift t) (counit t ≫ (fun_ _).hom)

/--
Definition of `whisker` / `whisker` 的定义

English:
definition whisker
  signature: (t : RightLift f g) {x : B} (h : x ⟶ c)
  body: .mk _ (α_ _ _ _).hom ≫ h ◁ t.counit

@[simp]

中文:
定义 whisker
  签名: (t : RightLift f g) {x : B} (h : x ⟶ c)
  定义体: .mk _ (α_ _ _ _).hom ≫ h ◁ t.counit

@[simp]

Depends on / 依赖: counit, t.counit
-/
def whisker (t : RightLift f g) {x : B} (h : x ⟶ c) : RightLift f (h ≫ g) :=
.mk _ (α_ _ _ _).hom ≫ h ◁ t.counit

@[simp]
/--
theorem `whisker_lift` / 定理 `whisker_lift`

English:
theorem whisker_lift
  given: (t : RightLift f g) {x : B} (h : x ⟶ c)
  proof: rfl

@[simp]

中文:
定理 whisker_lift
  条件: (t : RightLift f g) {x : B} (h : x ⟶ c)
  证明: rfl

@[simp]
-/
theorem whisker_lift (t : RightLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).lift = h ≫ t.lift :=
  rfl

@[simp]
/--
theorem `whisker_counit` / 定理 `whisker_counit`

English:
theorem whisker_counit
  given: (t : RightLift f g) {x : B} (h : x ⟶ c)
  proof: rfl

中文:
定理 whisker_counit
  条件: (t : RightLift f g) {x : B} (h : x ⟶ c)
  证明: rfl
-/
theorem whisker_counit (t : RightLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).counit = (α_ h t.lift f).hom ≫ h ◁ t.counit :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
/--
Definition of `whiskering` / `whiskering` 的定义

English:
definition whiskering
  signature: {x : B} (h : x ⟶ c)
  body: t.whisker h
map η := RightLift.homMk (h ◁ η.left) by
    dsimp only [whisker_lift, whisker_counit]
    rw [← RightLift.w η]
    simp [-RightLift.w]

中文:
定义 whiskering
  签名: {x : B} (h : x ⟶ c)
  定义体: t.whisker h
map η := RightLift.homMk (h ◁ η.left) by
    dsimp only [whisker_lift, whisker_counit]
    rw [← RightLift.w η]
    simp [-RightLift.w]

Depends on / 依赖: t.whisker, whisker
-/
def whiskering {x : B} (h : x ⟶ c) : RightLift f g ⥤ RightLift f (h ≫ g) where
  obj t := t.whisker h
map η := RightLift.homMk (h ◁ η.left) by
    dsimp only [whisker_lift, whisker_counit]
    rw [← RightLift.w η]
    simp [-RightLift.w]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between right lifts by cancelling the whiskered identities. -/
@[simps! left]
/--
Definition of `whiskerIdCancel` / `whiskerIdCancel` 的定义

English:
definition whiskerIdCancel
  body: RightLift.homMk ((fun_ _).inv ≫ τ.left)

中文:
定义 whiskerIdCancel
  定义体: RightLift.homMk ((fun_ _).inv ≫ τ.left)

Depends on / 依赖: HasLiftingProperty, RightLift, RightLift.homMk, fun_, of_left_iso
-/
def whiskerIdCancel
    (t : RightLift f (𝟙 c ≫ g)) {s : RightLift f g} (τ : s.whisker (𝟙 c) ⟶ t) :
    s ⟶ t.ofIdComp :=
  RightLift.homMk ((fun_ _).inv ≫ τ.left)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered lifts. -/
@[simps! left]
/--
Definition of `whiskerHom` / `whiskerHom` 的定义

English:
definition whiskerHom
  signature: (i : s ⟶ t) {x : B} (h : x ⟶ c)
  body: CostructuredArrow.homMk (h ◁ i.left) by
    rw [← cancel_epi (α_ h _ _).inv]
    calc
      _ = h ◁ (i.left ▷ f ≫ t.counit) := by simp [-RightLift.w]
      _ = h ◁ s.counit := congrArg (h ◁ ·) (RightLift.w i)
      _ = _ := by simp

中文:
定义 whiskerHom
  签名: (i : s ⟶ t) {x : B} (h : x ⟶ c)
  定义体: CostructuredArrow.homMk (h ◁ i.left) by
    rw [← cancel_epi (α_ h _ _).inv]
    calc
      _ = h ◁ (i.left ▷ f ≫ t.counit) := by simp [-RightLift.w]
      _ = h ◁ s.counit := congrArg (h ◁ ·) (RightLift.w i)
      _ = _ := by simp

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, RightLift, RightLift.w, cancel_epi, counit, i.left, s.counit, t.counit
-/
def whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) :
    s.whisker h ⟶ t.whisker h :=
CostructuredArrow.homMk (h ◁ i.left) by
    rw [← cancel_epi (α_ h _ _).inv]
    calc
      _ = h ◁ (i.left ▷ f ≫ t.counit) := by simp [-RightLift.w]
      _ = h ◁ s.counit := congrArg (h ◁ ·) (RightLift.w i)
      _ = _ := by simp

/--
Definition of `whiskerIso` / `whiskerIso` 的定义

English:
definition whiskerIso
  signature: (i : s ≅ t) {x : B} (h : x ⟶ c)
  body: Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (CostructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).left := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (CostructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).left := by

中文:
定义 whiskerIso
  签名: (i : s ≅ t) {x : B} (h : x ⟶ c)
  定义体: Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (CostructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).left := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (CostructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).left := by

Depends on / 依赖: CostructuredArrow, CostructuredArrow.hom_ext, Iso.hom_inv_id, Iso.inv_hom_id, Iso.mk, hom_ext, hom_inv_id, i.hom, i.inv, inv_hom_id, whiskerHom
-/
def whiskerIso (i : s ≅ t) {x : B} (h : x ⟶ c) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (CostructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).left := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (CostructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).left := by simp [-Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between right lifts induced by a left unitor. -/
@[simps! hom_left inv_left]
/--
Definition of `whiskerOfIdCompIsoSelf` / `whiskerOfIdCompIsoSelf` 的定义

English:
definition whiskerOfIdCompIsoSelf
  signature: (t : RightLift f g)
  body: CostructuredArrow.isoMk (fun_ (lift t))

中文:
定义 whiskerOfIdCompIsoSelf
  签名: (t : RightLift f g)
  定义体: CostructuredArrow.isoMk (fun_ (lift t))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, fun_
-/
def whiskerOfIdCompIsoSelf (t : RightLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  CostructuredArrow.isoMk (fun_ (lift t))

end RightLift

end Bicategory

end CategoryTheory
