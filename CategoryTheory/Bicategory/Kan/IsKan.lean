/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Extension

/-!
# Kan extensions and Kan lifts in bicategories

The left Kan extension of a 1-morphism `g : a ⟶ c` along a 1-morphism `f : a ⟶ b` is the initial
object in the category of left extensions `LeftExtension f g`. The universal property can be
accessed by the following definition and lemmas:
* `LeftExtension.IsKan.desc`: the family of 2-morphisms out of the left Kan extension.
* `LeftExtension.IsKan.fac`: the unit of any left extension factors through the left Kan extension.
* `LeftExtension.IsKan.hom_ext`: two 2-morphisms out of the left Kan extension are equal if their
  compositions with each unit are equal.

We also define left Kan lifts, right Kan extensions, and right Kan lifts.

## Implementation Notes

We use the Is-Has design pattern, which is used for the implementation of limits and colimits in
the category theory library. This means that `IsKan t` is a structure containing the data of
2-morphisms which ensure that `t` is a Kan extension, while `HasLeftKanExtension f g`
(and similarly for lifts) defined in `CategoryTheory.Bicategory.Kan.HasKan`
is a `Prop`-valued typeclass asserting that a Kan extension of `g` along `f` exists.

We define `LeftExtension.IsKan t` for an extension `t : LeftExtension f g` (which is an
abbreviation of `t : StructuredArrow g (precomp _ f)`) to be an abbreviation for
`StructuredArrow.IsUniversal t`. This means that we can use the definitions and lemmas living
in the namespace `StructuredArrow.IsUniversal`.

## References
https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/--
Definition of `IsKan` / `IsKan` 的定义

English:
abbreviation IsKan
  signature: (t : LeftExtension f g)
  body: t.IsUniversal

中文:
缩写 IsKan
  签名: (t : LeftExtension f g)
  定义体: t.IsUniversal

Depends on / 依赖: IsUniversal, t.IsUniversal
-/
abbrev IsKan (t : LeftExtension f g) := t.IsUniversal

/--
Definition of `IsAbsKan` / `IsAbsKan` 的定义

English:
abbreviation IsAbsKan
  signature: (t : LeftExtension f g)
  body: forall {x : B} (h : c ⟶ x), IsKan (t.whisker h)

中文:
缩写 IsAbsKan
  签名: (t : LeftExtension f g)
  定义体: forall {x : B} (h : c ⟶ x), IsKan (t.whisker h)

Depends on / 依赖: t.whisker, whisker
-/
abbrev IsAbsKan (t : LeftExtension f g) :=
  forall {x : B} (h : c ⟶ x), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftExtension f g}

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (desc : forall s, t ⟶ s) (w : forall s τ, τ = desc s)
  body: .ofUniqueHom desc w

中文:
缩写 mk
  签名: (desc : 对任意 s, t ⟶ s) (w : 对任意 s τ, τ = desc s)
  定义体: .ofUniqueHom desc w

Depends on / 依赖: ofUniqueHom
-/
abbrev mk (desc : forall s, t ⟶ s) (w : forall s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (H : IsKan t) (s : LeftExtension f g)
  body: StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]

中文:
缩写 desc
  签名: (H : IsKan t) (s : LeftExtension f g)
  定义体: StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]

Depends on / 依赖: IsUniversal, StructuredArrow, StructuredArrow.IsUniversal.desc
-/
abbrev desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension :=
  StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]
/--
theorem `fac` / 定理 `fac`

English:
theorem fac
  given: (H : IsKan t) (s : LeftExtension f g)
  proof: StructuredArrow.IsUniversal.fac H s

中文:
定理 fac
  条件: (H : IsKan t) (s : LeftExtension f g)
  证明: StructuredArrow.IsUniversal.fac H s

Depends on / 依赖: IsUniversal, StructuredArrow, StructuredArrow.IsUniversal.fac, createsLimitOfReflectsIso, isLimit, isValidLift, liftedCone, limit.isLimit
-/
theorem fac (H : IsKan t) (s : LeftExtension f g) :
    t.unit ≫ f ◁ H.desc s = s.unit :=
  StructuredArrow.IsUniversal.fac H s

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
  proof: StructuredArrow.IsUniversal.hom_ext H w

中文:
定理 hom_ext
  结论: (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
  证明: StructuredArrow.IsUniversal.hom_ext H w

Depends on / 依赖: IsUniversal, StructuredArrow, StructuredArrow.IsUniversal.hom_ext, hom_ext
-/
theorem hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
    (w : t.unit ≫ f ◁ τ = t.unit ≫ f ◁ τ') : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w

/--
Definition of `uniqueUpToIso` / `uniqueUpToIso` 的定义

English:
definition uniqueUpToIso
  signature: (P : IsKan s) (Q : IsKan t)
  body: Limits.IsInitial.uniqueUpToIso P Q

@[simp]

中文:
定义 uniqueUpToIso
  签名: (P : IsKan s) (Q : IsKan t)
  定义体: Limits.IsInitial.uniqueUpToIso P Q

@[simp]

Depends on / 依赖: Elements, F.representableBy, Functor, Functor.Elements.isInitialOfRepresentableBy, IsInitial, Limits, Limits.IsInitial.uniqueUpToIso, hasInitial, isInitialOfRepresentableBy, representableBy, uniqueUpToIso
-/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q

@[simp]
/--
theorem `uniqueUpToIso_hom_right` / 定理 `uniqueUpToIso_hom_right`

English:
theorem uniqueUpToIso_hom_right
  given: (P : IsKan s) (Q : IsKan t)
  proof: rfl

@[simp]

中文:
定理 uniqueUpToIso_hom_right
  条件: (P : IsKan s) (Q : IsKan t)
  证明: rfl

@[simp]

Depends on / 依赖: Elements, F.corepresentableBy, Functor, Functor.Elements.isInitialOfCorepresentableBy, corepresentableBy, hasInitial, isInitialOfCorepresentableBy
-/
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl

@[simp]
/--
theorem `uniqueUpToIso_inv_right` / 定理 `uniqueUpToIso_inv_right`

English:
theorem uniqueUpToIso_inv_right
  given: (P : IsKan s) (Q : IsKan t)
  proof: rfl

中文:
定理 uniqueUpToIso_inv_right
  条件: (P : IsKan s) (Q : IsKan t)
  证明: rfl
-/
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl

/--
Definition of `ofIsoKan` / `ofIsoKan` 的定义

English:
definition ofIsoKan
  signature: (P : IsKan s) (i : s ≅ t)
  body: Limits.IsInitial.ofIso P i

中文:
定义 ofIsoKan
  签名: (P : IsKan s) (i : s ≅ t)
  定义体: Limits.IsInitial.ofIso P i

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.ofIso
-/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofCompId` / `ofCompId` 的定义

English:
definition ofCompId
  signature: (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t)
  body: .mk (fun s => t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftExtension.w τ]

中文:
定义 ofCompId
  签名: (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t)
  定义体: .mk (fun s => t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftExtension.w τ]

Depends on / 依赖: LeftExtension, LeftExtension.w, P.hom_ext, P.to, hom_ext, s.whisker, t.whiskerIdCancel, whisker, whiskerIdCancel
-/
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t) : IsKan t.ofCompId :=
.mk (fun s => t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftExtension.w τ]

/--
Definition of `whiskerOfCommute` / `whiskerOfCommute` 的定义

English:
definition whiskerOfCommute
  signature: (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
  body: P.ofIsoKan whiskerIso i h

中文:
定义 whiskerOfCommute
  签名: (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
  定义体: P.ofIsoKan whiskerIso i h

Depends on / 依赖: P.ofIsoKan, ofIsoKan, whiskerIso
-/
def whiskerOfCommute (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
P.ofIsoKan whiskerIso i h

end IsKan

namespace IsAbsKan

variable {s t : LeftExtension f g}

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h))
  body: (H h).desc s

中文:
缩写 desc
  签名: (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h))
  定义体: (H h).desc s
-/
abbrev desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h)) :
    t.extension ≫ h ⟶ s.extension :=
  (H h).desc s

/--
Definition of `isKan` / `isKan` 的定义

English:
definition isKan
  signature: (H : IsAbsKan t)
  body: ((H (𝟙 c)).ofCompId _).ofIsoKan whiskerOfCompIdIsoSelf t

中文:
定义 isKan
  签名: (H : IsAbsKan t)
  定义体: ((H (𝟙 c)).ofCompId _).ofIsoKan whiskerOfCompIdIsoSelf t

Depends on / 依赖: ofCompId, ofIsoKan, whiskerOfCompIdIsoSelf
-/
def isKan (H : IsAbsKan t) : IsKan t :=
((H (𝟙 c)).ofCompId _).ofIsoKan whiskerOfCompIdIsoSelf t

/--
Definition of `ofIsoAbsKan` / `ofIsoAbsKan` 的定义

English:
definition ofIsoAbsKan
  signature: (P : IsAbsKan s) (i : s ≅ t)
  body: fun h => (P h).ofIsoKan (whiskerIso i h)

中文:
定义 ofIsoAbsKan
  签名: (P : IsAbsKan s) (i : s ≅ t)
  定义体: fun h => (P h).ofIsoKan (whiskerIso i h)

Depends on / 依赖: ofIsoKan, whiskerIso
-/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h => (P h).ofIsoKan (whiskerIso i h)

end IsAbsKan

end LeftExtension

namespace LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/--
Definition of `IsKan` / `IsKan` 的定义

English:
abbreviation IsKan
  signature: (t : LeftLift f g)
  body: t.IsUniversal

中文:
缩写 IsKan
  签名: (t : LeftLift f g)
  定义体: t.IsUniversal

Depends on / 依赖: IsUniversal, t.IsUniversal
-/
abbrev IsKan (t : LeftLift f g) := t.IsUniversal

/--
Definition of `IsAbsKan` / `IsAbsKan` 的定义

English:
abbreviation IsAbsKan
  signature: (t : LeftLift f g)
  body: forall {x : B} (h : x ⟶ c), IsKan (t.whisker h)

中文:
缩写 IsAbsKan
  签名: (t : LeftLift f g)
  定义体: forall {x : B} (h : x ⟶ c), IsKan (t.whisker h)

Depends on / 依赖: t.whisker, whisker
-/
abbrev IsAbsKan (t : LeftLift f g) :=
  forall {x : B} (h : x ⟶ c), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftLift f g}

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (desc : forall s, t ⟶ s) (w : forall s τ, τ = desc s)
  body: .ofUniqueHom desc w

中文:
缩写 mk
  签名: (desc : 对任意 s, t ⟶ s) (w : 对任意 s τ, τ = desc s)
  定义体: .ofUniqueHom desc w

Depends on / 依赖: ofUniqueHom
-/
abbrev mk (desc : forall s, t ⟶ s) (w : forall s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (H : IsKan t) (s : LeftLift f g)
  body: StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]

中文:
缩写 desc
  签名: (H : IsKan t) (s : LeftLift f g)
  定义体: StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]

Depends on / 依赖: IsUniversal, StructuredArrow, StructuredArrow.IsUniversal.desc
-/
abbrev desc (H : IsKan t) (s : LeftLift f g) : t.lift ⟶ s.lift :=
  StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]
/--
theorem `fac` / 定理 `fac`

English:
theorem fac
  given: (H : IsKan t) (s : LeftLift f g)
  proof: StructuredArrow.IsUniversal.fac H s

中文:
定理 fac
  条件: (H : IsKan t) (s : LeftLift f g)
  证明: StructuredArrow.IsUniversal.fac H s

Depends on / 依赖: IsUniversal, StructuredArrow, StructuredArrow.IsUniversal.fac
-/
theorem fac (H : IsKan t) (s : LeftLift f g) :
    t.unit ≫ H.desc s ▷ f = s.unit :=
  StructuredArrow.IsUniversal.fac H s

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k}
  proof: StructuredArrow.IsUniversal.hom_ext H w

中文:
定理 hom_ext
  结论: (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k}
  证明: StructuredArrow.IsUniversal.hom_ext H w

Depends on / 依赖: IsUniversal, StructuredArrow, StructuredArrow.IsUniversal.hom_ext, hom_ext
-/
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k}
    (w : t.unit ≫ τ ▷ f = t.unit ≫ τ' ▷ f) : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w

/--
Definition of `uniqueUpToIso` / `uniqueUpToIso` 的定义

English:
definition uniqueUpToIso
  signature: (P : IsKan s) (Q : IsKan t)
  body: Limits.IsInitial.uniqueUpToIso P Q

@[simp]

中文:
定义 uniqueUpToIso
  签名: (P : IsKan s) (Q : IsKan t)
  定义体: Limits.IsInitial.uniqueUpToIso P Q

@[simp]

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.uniqueUpToIso, uniqueUpToIso
-/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q

@[simp]
/--
theorem `uniqueUpToIso_hom_right` / 定理 `uniqueUpToIso_hom_right`

English:
theorem uniqueUpToIso_hom_right
  given: (P : IsKan s) (Q : IsKan t)
  proof: rfl

@[simp]

中文:
定理 uniqueUpToIso_hom_right
  条件: (P : IsKan s) (Q : IsKan t)
  证明: rfl

@[simp]
-/
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl

@[simp]
/--
theorem `uniqueUpToIso_inv_right` / 定理 `uniqueUpToIso_inv_right`

English:
theorem uniqueUpToIso_inv_right
  given: (P : IsKan s) (Q : IsKan t)
  proof: rfl

中文:
定理 uniqueUpToIso_inv_right
  条件: (P : IsKan s) (Q : IsKan t)
  证明: rfl
-/
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl

/--
Definition of `ofIsoKan` / `ofIsoKan` 的定义

English:
definition ofIsoKan
  signature: (P : IsKan s) (i : s ≅ t)
  body: Limits.IsInitial.ofIso P i

中文:
定义 ofIsoKan
  签名: (P : IsKan s) (i : s ≅ t)
  定义体: Limits.IsInitial.ofIso P i

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.ofIso
-/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofIdComp` / `ofIdComp` 的定义

English:
definition ofIdComp
  signature: (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t)
  body: .mk (fun s => t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftLift.w τ]

中文:
定义 ofIdComp
  签名: (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t)
  定义体: .mk (fun s => t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftLift.w τ]

Depends on / 依赖: LeftLift, LeftLift.w, P.hom_ext, P.to, hom_ext, s.whisker, t.whiskerIdCancel, whisker, whiskerIdCancel
-/
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
.mk (fun s => t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftLift.w τ]

/--
Definition of `whiskerOfCommute` / `whiskerOfCommute` 的定义

English:
definition whiskerOfCommute
  signature: (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
  body: P.ofIsoKan whiskerIso i h

中文:
定义 whiskerOfCommute
  签名: (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
  定义体: P.ofIsoKan whiskerIso i h

Depends on / 依赖: P.ofIsoKan, ofIsoKan, whiskerIso
-/
def whiskerOfCommute (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
P.ofIsoKan whiskerIso i h

end IsKan

namespace IsAbsKan

variable {s t : LeftLift f g}

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g))
  body: (H h).desc s

中文:
缩写 desc
  签名: (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g))
  定义体: (H h).desc s
-/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g)) :
    h ≫ t.lift ⟶ s.lift :=
  (H h).desc s

/--
Definition of `isKan` / `isKan` 的定义

English:
definition isKan
  signature: (H : IsAbsKan t)
  body: ((H (𝟙 c)).ofIdComp _).ofIsoKan whiskerOfIdCompIsoSelf t

中文:
定义 isKan
  签名: (H : IsAbsKan t)
  定义体: ((H (𝟙 c)).ofIdComp _).ofIsoKan whiskerOfIdCompIsoSelf t

Depends on / 依赖: ofIdComp, ofIsoKan, whiskerOfIdCompIsoSelf
-/
def isKan (H : IsAbsKan t) : IsKan t :=
((H (𝟙 c)).ofIdComp _).ofIsoKan whiskerOfIdCompIsoSelf t

/--
Definition of `ofIsoAbsKan` / `ofIsoAbsKan` 的定义

English:
definition ofIsoAbsKan
  signature: (P : IsAbsKan s) (i : s ≅ t)
  body: fun h => (P h).ofIsoKan (whiskerIso i h)

中文:
定义 ofIsoAbsKan
  签名: (P : IsAbsKan s) (i : s ≅ t)
  定义体: fun h => (P h).ofIsoKan (whiskerIso i h)

Depends on / 依赖: ofIsoKan, whiskerIso
-/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h => (P h).ofIsoKan (whiskerIso i h)

end IsAbsKan

end LeftLift

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/--
Definition of `IsKan` / `IsKan` 的定义

English:
abbreviation IsKan
  signature: (t : RightExtension f g)
  body: t.IsUniversal

中文:
缩写 IsKan
  签名: (t : RightExtension f g)
  定义体: t.IsUniversal

Depends on / 依赖: IsUniversal, t.IsUniversal
-/
abbrev IsKan (t : RightExtension f g) := t.IsUniversal

end RightExtension

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/--
Definition of `IsKan` / `IsKan` 的定义

English:
abbreviation IsKan
  signature: (t : RightLift f g)
  body: t.IsUniversal

中文:
缩写 IsKan
  签名: (t : RightLift f g)
  定义体: t.IsUniversal

Depends on / 依赖: IsUniversal, t.IsUniversal
-/
abbrev IsKan (t : RightLift f g) := t.IsUniversal

/--
Definition of `IsAbsKan` / `IsAbsKan` 的定义

English:
abbreviation IsAbsKan
  signature: (t : RightLift f g)
  body: forall {x : B} (h : x ⟶ c), IsKan (t.whisker h)

中文:
缩写 IsAbsKan
  签名: (t : RightLift f g)
  定义体: forall {x : B} (h : x ⟶ c), IsKan (t.whisker h)

Depends on / 依赖: t.whisker, whisker
-/
abbrev IsAbsKan (t : RightLift f g) :=
  forall {x : B} (h : x ⟶ c), IsKan (t.whisker h)

namespace IsKan

variable {s t : RightLift f g}

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (desc : forall s, s ⟶ t) (w : forall s τ, τ = desc s)
  body: .ofUniqueHom desc w

中文:
缩写 mk
  签名: (desc : 对任意 s, s ⟶ t) (w : 对任意 s τ, τ = desc s)
  定义体: .ofUniqueHom desc w

Depends on / 依赖: ofUniqueHom
-/
abbrev mk (desc : forall s, s ⟶ t) (w : forall s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (H : IsKan t) (s : RightLift f g)
  body: CostructuredArrow.IsUniversal.lift H s

@[reassoc (attr := simp)]

中文:
缩写 desc
  签名: (H : IsKan t) (s : RightLift f g)
  定义体: CostructuredArrow.IsUniversal.lift H s

@[reassoc (attr := simp)]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.IsUniversal.lift, IsUniversal
-/
abbrev desc (H : IsKan t) (s : RightLift f g) : s.lift ⟶ t.lift :=
  CostructuredArrow.IsUniversal.lift H s

@[reassoc (attr := simp)]
/--
theorem `fac` / 定理 `fac`

English:
theorem fac
  given: (H : IsKan t) (s : RightLift f g)
  proof: CostructuredArrow.IsUniversal.fac H s

中文:
定理 fac
  条件: (H : IsKan t) (s : RightLift f g)
  证明: CostructuredArrow.IsUniversal.fac H s

Depends on / 依赖: CostructuredArrow, CostructuredArrow.IsUniversal.fac, IsUniversal
-/
theorem fac (H : IsKan t) (s : RightLift f g) :
    H.desc s ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.IsUniversal.fac H s

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (H : IsKan t) {k : c ⟶ b} {τ τ' : k ⟶ t.lift}
  proof: CostructuredArrow.IsUniversal.hom_ext H w

中文:
定理 hom_ext
  结论: (H : IsKan t) {k : c ⟶ b} {τ τ' : k ⟶ t.lift}
  证明: CostructuredArrow.IsUniversal.hom_ext H w

Depends on / 依赖: CostructuredArrow, CostructuredArrow.IsUniversal.hom_ext, IsUniversal, hom_ext
-/
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : k ⟶ t.lift}
    (w : τ ▷ f ≫ t.counit = τ' ▷ f ≫ t.counit) : τ = τ' :=
  CostructuredArrow.IsUniversal.hom_ext H w

/--
Definition of `uniqueUpToIso` / `uniqueUpToIso` 的定义

English:
definition uniqueUpToIso
  signature: (P : IsKan s) (Q : IsKan t)
  body: Limits.IsTerminal.uniqueUpToIso P Q

@[simp]

中文:
定义 uniqueUpToIso
  签名: (P : IsKan s) (Q : IsKan t)
  定义体: Limits.IsTerminal.uniqueUpToIso P Q

@[simp]

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.uniqueUpToIso, uniqueUpToIso
-/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsTerminal.uniqueUpToIso P Q

@[simp]
/--
theorem `uniqueUpToIso_hom_left` / 定理 `uniqueUpToIso_hom_left`

English:
theorem uniqueUpToIso_hom_left
  given: (P : IsKan s) (Q : IsKan t)
  proof: rfl

@[simp]

中文:
定理 uniqueUpToIso_hom_left
  条件: (P : IsKan s) (Q : IsKan t)
  证明: rfl

@[simp]
-/
theorem uniqueUpToIso_hom_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.left = Q.desc s := rfl

@[simp]
/--
theorem `uniqueUpToIso_inv_left` / 定理 `uniqueUpToIso_inv_left`

English:
theorem uniqueUpToIso_inv_left
  given: (P : IsKan s) (Q : IsKan t)
  proof: rfl

中文:
定理 uniqueUpToIso_inv_left
  条件: (P : IsKan s) (Q : IsKan t)
  证明: rfl
-/
theorem uniqueUpToIso_inv_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.left = P.desc t := rfl

/--
Definition of `ofIsoKan` / `ofIsoKan` 的定义

English:
definition ofIsoKan
  signature: (P : IsKan s) (i : s ≅ t)
  body: Limits.IsTerminal.ofIso P i

中文:
定义 ofIsoKan
  签名: (P : IsKan s) (i : s ≅ t)
  定义体: Limits.IsTerminal.ofIso P i

Depends on / 依赖: IsTerminal, Limits, Limits.IsTerminal.ofIso
-/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsTerminal.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofIdComp` / `ofIdComp` 的定义

English:
definition ofIdComp
  signature: (t : RightLift f (𝟙 c ≫ g)) (P : IsKan t)
  body: .mk (fun s => t.whiskerIdCancel <| P.from (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← RightLift.w τ]

中文:
定义 ofIdComp
  签名: (t : RightLift f (𝟙 c ≫ g)) (P : IsKan t)
  定义体: .mk (fun s => t.whiskerIdCancel <| P.from (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← RightLift.w τ]

Depends on / 依赖: P.from, P.hom_ext, RightLift, RightLift.w, hom_ext, s.whisker, t.whiskerIdCancel, whisker, whiskerIdCancel
-/
def ofIdComp (t : RightLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
.mk (fun s => t.whiskerIdCancel <| P.from (s.whisker (𝟙 c))) by
    intro s τ
    ext
    apply P.hom_ext
    simp [← RightLift.w τ]

/--
Definition of `whiskerOfCommute` / `whiskerOfCommute` 的定义

English:
definition whiskerOfCommute
  signature: (s t : RightLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
  body: P.ofIsoKan whiskerIso i h

中文:
定义 whiskerOfCommute
  签名: (s t : RightLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
  定义体: P.ofIsoKan whiskerIso i h

Depends on / 依赖: P.ofIsoKan, ofIsoKan, whiskerIso
-/
def whiskerOfCommute (s t : RightLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
P.ofIsoKan whiskerIso i h

end IsKan

namespace IsAbsKan

variable {s t : RightLift f g}

/--
Definition of `desc` / `desc` 的定义

English:
abbreviation desc
  signature: (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : RightLift f (h ≫ g))
  body: (H h).desc s

中文:
缩写 desc
  签名: (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : RightLift f (h ≫ g))
  定义体: (H h).desc s
-/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : RightLift f (h ≫ g)) :
    s.lift ⟶ h ≫ t.lift :=
  (H h).desc s

/--
Definition of `isKan` / `isKan` 的定义

English:
definition isKan
  signature: (H : IsAbsKan t)
  body: ((H (𝟙 c)).ofIdComp _).ofIsoKan whiskerOfIdCompIsoSelf t

中文:
定义 isKan
  签名: (H : IsAbsKan t)
  定义体: ((H (𝟙 c)).ofIdComp _).ofIsoKan whiskerOfIdCompIsoSelf t

Depends on / 依赖: ofIdComp, ofIsoKan, whiskerOfIdCompIsoSelf
-/
def isKan (H : IsAbsKan t) : IsKan t :=
((H (𝟙 c)).ofIdComp _).ofIsoKan whiskerOfIdCompIsoSelf t

/--
Definition of `ofIsoAbsKan` / `ofIsoAbsKan` 的定义

English:
definition ofIsoAbsKan
  signature: (P : IsAbsKan s) (i : s ≅ t)
  body: fun h => (P h).ofIsoKan (whiskerIso i h)

中文:
定义 ofIsoAbsKan
  签名: (P : IsAbsKan s) (i : s ≅ t)
  定义体: fun h => (P h).ofIsoKan (whiskerIso i h)

Depends on / 依赖: ofIsoKan, whiskerIso
-/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h => (P h).ofIsoKan (whiskerIso i h)

end IsAbsKan

end RightLift

end Bicategory

end CategoryTheory
