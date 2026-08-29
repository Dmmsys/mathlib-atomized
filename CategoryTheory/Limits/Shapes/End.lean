/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Ends and coends

In this file, given a functor `F : Jᵒᵖ ⥤ J ⥤ C`, we define its end `end_ F`,
which is a suitable multiequalizer of the objects `(F.obj (op j)).obj j` for all `j : J`.
For this shape of limits, cones are named wedges: the corresponding type is `Wedge F`.

We also introduce `coend F` as multicoequalizers of
`(F.obj (op j)).obj j` for all `j : J`. In these cases, cocones are named cowedges.

## References
* https://ncatlab.org/nlab/show/end

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : Jᵒᵖ ⥤ J ⥤ C)

variable (J) in
/-- The shape of multiequalizer diagrams involved in the definition of ends. -/
@[simps]
/--
Definition of `multicospanShapeEnd` / `multicospanShapeEnd` 的定义

English:
definition multicospanShapeEnd
  signature: : MulticospanShape where
  body: J
  R := Arrow J
  fst f := f.left
  snd f := f.right

中文:
定义 multicospanShapeEnd
  签名: : MulticospanShape where
  定义体: J
  R := Arrow J
  fst f := f.left
  snd f := f.right
-/
def multicospanShapeEnd : MulticospanShape where
  L := J
  R := Arrow J
  fst f := f.left
  snd f := f.right

variable (J) in
/-- The shape of multicoequalizer diagrams involved in the definition of coends. -/
@[simps]
/--
Definition of `multispanShapeCoend` / `multispanShapeCoend` 的定义

English:
definition multispanShapeCoend
  signature: : MultispanShape where
  body: Arrow J
  R := J
  fst f := f.left
  snd f := f.right

中文:
定义 multispanShapeCoend
  签名: : MultispanShape where
  定义体: Arrow J
  R := J
  fst f := f.left
  snd f := f.right
-/
def multispanShapeCoend : MultispanShape where
  L := Arrow J
  R := J
  fst f := f.left
  snd f := f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multicospan index which shall be used
to define the end of `F`. -/
@[simps]
/--
Definition of `multicospanIndexEnd` / `multicospanIndexEnd` 的定义

English:
definition multicospanIndexEnd
  signature: : MulticospanIndex (multicospanShapeEnd J) C where
  body: (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

中文:
定义 multicospanIndexEnd
  签名: : MulticospanIndex (multicospanShapeEnd J) C where
  定义体: (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

Depends on / 依赖: F.obj
-/
def multicospanIndexEnd : MulticospanIndex (multicospanShapeEnd J) C where
  left j := (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multispan used to define the coend
of `F`. -/
@[simps]
/--
Definition of `multispanIndexCoend` / `multispanIndexCoend` 的定义

English:
definition multispanIndexCoend
  signature: : MultispanIndex (multispanShapeCoend J) C where
  body: (F.obj (op f.right)).obj f.left
  right j := (F.obj (op j)).obj j
  fst f := (F.map f.hom.op).app f.left
  snd f := (F.obj (op f.right)).map f.hom

中文:
定义 multispanIndexCoend
  签名: : MultispanIndex (multispanShapeCoend J) C where
  定义体: (F.obj (op f.right)).obj f.left
  right j := (F.obj (op j)).obj j
  fst f := (F.map f.hom.op).app f.left
  snd f := (F.obj (op f.right)).map f.hom

Depends on / 依赖: F.obj, f.left, f.right
-/
def multispanIndexCoend : MultispanIndex (multispanShapeCoend J) C where
  left f := (F.obj (op f.right)).obj f.left
  right j := (F.obj (op j)).obj j
  fst f := (F.map f.hom.op).app f.left
  snd f := (F.obj (op f.right)).map f.hom

/--
Definition of `Wedge` / `Wedge` 的定义

English:
abbreviation Wedge
  body: Multifork (multicospanIndexEnd F)

中文:
缩写 Wedge
  定义体: Multifork (multicospanIndexEnd F)

Depends on / 依赖: Multifork, multicospanIndexEnd
-/
abbrev Wedge := Multifork (multicospanIndexEnd F)

namespace Wedge

variable {F}

/-- A variant of `CategoryTheory.Limits.Cone.ext` specialized to produce
isomorphisms of wedges. -/
@[simps!]
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt)
  body: Cone.ext e (fun j =>
    match j with
    | .left _ => he _
    | .right f => by simpa using! (he f.left) =≫ _)

中文:
定义 ext
  签名: {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt)
  定义体: Cone.ext e (fun j =>
    match j with
    | .left _ => he _
    | .right f => by simpa using! (he f.left) =≫ _)

Depends on / 依赖: Cone.ext, cat_disch, f.left
-/
def ext {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt)
    (he : forall j : J, W₁.ι j = e.hom ≫ W₂.ι j := by cat_disch) : W₁ ≅ W₂ :=
  Cone.ext e (fun j =>
    match j with
    | .left _ => he _
    | .right f => by simpa using! (he f.left) =≫ _)

section Constructor

variable (pt : C) (π : forall (j : J), pt ⟶ (F.obj (op j)).obj j)
  (hπ : forall ⦃i j : J⦄ (f : i ⟶ j), π i ≫ (F.obj (op i)).map f = π j ≫ (F.map f.op).app j)

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: : Wedge F
  body: Multifork.ofι _ pt π (fun f => hπ f.hom)

@[simp]

中文:
缩写 mk
  签名: : Wedge F
  定义体: Multifork.ofι _ pt π (fun f => hπ f.hom)

@[simp]

Depends on / 依赖: Multifork, Multifork.of, f.hom
-/
abbrev mk : Wedge F :=
  Multifork.ofι _ pt π (fun f => hπ f.hom)

@[simp]
/--
lemma `mk_ι` / 引理 `mk_ι`

English:
lemma mk_ι
  given: (j : J)
  statement: (mk pt π hπ).ι j = π j
  proof: rfl

中文:
引理 mk_ι
  条件: (j : J)
  结论: (mk pt π hπ).ι j = π j
  证明: rfl
-/
lemma mk_ι (j : J) : (mk pt π hπ).ι j = π j := rfl

end Constructor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `condition` / 引理 `condition`

English:
lemma condition
  given: (c : Wedge F) {i j : J} (f : i ⟶ j)
  proof: Multifork.condition c (Arrow.mk f)

中文:
引理 condition
  条件: (c : Wedge F) {i j : J} (f : i ⟶ j)
  证明: Multifork.condition c (Arrow.mk f)

Depends on / 依赖: Arrow.mk, Multifork, Multifork.condition, condition
-/
lemma condition (c : Wedge F) {i j : J} (f : i ⟶ j) :
    c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j :=
  Multifork.condition c (Arrow.mk f)

namespace IsLimit

variable {c : Wedge F} (hc : IsLimit c)

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : forall j, f ≫ c.ι j = g ≫ c.ι j)
  proof: Multifork.IsLimit.hom_ext hc h

中文:
引理 hom_ext
  条件: (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : 对任意 j, f ≫ c.ι j = g ≫ c.ι j)
  证明: Multifork.IsLimit.hom_ext hc h

Depends on / 依赖: IsLimit, Multifork, Multifork.IsLimit.hom_ext, hom_ext
-/
lemma hom_ext (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : forall j, f ≫ c.ι j = g ≫ c.ι j) :
    f = g :=
  Multifork.IsLimit.hom_ext hc h

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (hc : IsLimit c) {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j)
  body: Multifork.IsLimit.lift hc f (fun _ => hf _)

@[reassoc (attr := simp)]

中文:
定义 lift
  签名: (hc : IsLimit c) {X : C} (f : 对任意 j, X ⟶ (F.obj (op j)).obj j)
  定义体: Multifork.IsLimit.lift hc f (fun _ => hf _)

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, Multifork, Multifork.IsLimit.lift
-/
def lift (hc : IsLimit c) {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j)
    (hf : forall ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) :
    X ⟶ c.pt :=
  Multifork.IsLimit.lift hc f (fun _ => hf _)

@[reassoc (attr := simp)]
/--
lemma `lift_ι` / 引理 `lift_ι`

English:
lemma lift_ι
  statement: (hc : IsLimit c) {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j)
  proof: by
  apply IsLimit.fac

中文:
引理 lift_ι
  结论: (hc : IsLimit c) {X : C} (f : 对任意 j, X ⟶ (F.obj (op j)).obj j)
  证明: by
  apply IsLimit.fac

Depends on / 依赖: IsLimit, IsLimit.fac
-/
lemma lift_ι (hc : IsLimit c) {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j)
    (hf : forall ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) (j : J) :
    lift hc f hf ≫ c.ι j = f j := by
  apply IsLimit.fac


end IsLimit

end Wedge

/--
Definition of `Cowedge` / `Cowedge` 的定义

English:
abbreviation Cowedge
  body: Multicofork (multispanIndexCoend F)

中文:
缩写 Cowedge
  定义体: Multicofork (multispanIndexCoend F)

Depends on / 依赖: Multicofork, multispanIndexCoend
-/
abbrev Cowedge := Multicofork (multispanIndexCoend F)

namespace Cowedge

variable {F}

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `CategoryTheory.Limits.Cocone.ext` specialized to produce
isomorphisms of cowedges. -/
@[simps!]
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt)
  body: Cocone.ext e (fun j =>
    match j with
    | .right _ => he _
    | .left f => by simpa using! _ ≫= (he f.left))

中文:
定义 ext
  签名: {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt)
  定义体: Cocone.ext e (fun j =>
    match j with
    | .right _ => he _
    | .left f => by simpa using! _ ≫= (he f.left))

Depends on / 依赖: Cocone, Cocone.ext, cat_disch, f.left
-/
def ext {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt)
    (he : forall j : J, W₁.π j ≫ e.hom = W₂.π j := by cat_disch) : W₁ ≅ W₂ :=
  Cocone.ext e (fun j =>
    match j with
    | .right _ => he _
    | .left f => by simpa using! _ ≫= (he f.left))

section Constructor

variable (pt : C) (ι : forall (j : J), (F.obj (op j)).obj j ⟶ pt)
  (hι : forall ⦃i j : J⦄ (f : i ⟶ j), (F.map f.op).app i ≫ ι i = (F.obj (op j)).map f ≫ ι j)

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: : Cowedge F
  body: Multicofork.ofπ _ pt ι (fun f => hι f.hom)

@[simp]

中文:
缩写 mk
  签名: : Cowedge F
  定义体: Multicofork.ofπ _ pt ι (fun f => hι f.hom)

@[simp]

Depends on / 依赖: Multicofork, Multicofork.of, f.hom
-/
abbrev mk : Cowedge F :=
  Multicofork.ofπ _ pt ι (fun f => hι f.hom)

@[simp]
/--
lemma `mk_π` / 引理 `mk_π`

English:
lemma mk_π
  given: (j : J)
  statement: (mk pt ι hι).π j = ι j
  proof: rfl

中文:
引理 mk_π
  条件: (j : J)
  结论: (mk pt ι hι).π j = ι j
  证明: rfl
-/
lemma mk_π (j : J) : (mk pt ι hι).π j = ι j := rfl

end Constructor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `condition` / 引理 `condition`

English:
lemma condition
  given: (c : Cowedge F) {i j : J} (f : i ⟶ j)
  proof: Multicofork.condition c (Arrow.mk f)

中文:
引理 condition
  条件: (c : Cowedge F) {i j : J} (f : i ⟶ j)
  证明: Multicofork.condition c (Arrow.mk f)

Depends on / 依赖: Arrow.mk, Multicofork, Multicofork.condition, condition
-/
lemma condition (c : Cowedge F) {i j : J} (f : i ⟶ j) :
    (F.map f.op).app i ≫ c.π i = (F.obj (op j)).map f ≫ c.π j :=
  Multicofork.condition c (Arrow.mk f)

namespace IsColimit

variable {c : Cowedge F} (hc : IsColimit c)

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: (hc : IsColimit c) {X : C} {f g : c.pt ⟶ X} (h : forall j, c.π j ≫ f = c.π j ≫ g)
  proof: Multicofork.IsColimit.hom_ext hc h

中文:
引理 hom_ext
  条件: (hc : IsColimit c) {X : C} {f g : c.pt ⟶ X} (h : 对任意 j, c.π j ≫ f = c.π j ≫ g)
  证明: Multicofork.IsColimit.hom_ext hc h

Depends on / 依赖: IsColimit, Multicofork, Multicofork.IsColimit.hom_ext, hom_ext
-/
lemma hom_ext (hc : IsColimit c) {X : C} {f g : c.pt ⟶ X} (h : forall j, c.π j ≫ f = c.π j ≫ g) :
    f = g :=
  Multicofork.IsColimit.hom_ext hc h

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (hc : IsColimit c) {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X)
  body: Multicofork.IsColimit.desc hc f (fun _ => hf _)

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: (hc : IsColimit c) {X : C} (f : 对任意 j, (F.obj (op j)).obj j ⟶ X)
  定义体: Multicofork.IsColimit.desc hc f (fun _ => hf _)

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, Multicofork, Multicofork.IsColimit.desc
-/
def desc (hc : IsColimit c) {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X)
    (hf : forall ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j) :
    c.pt ⟶ X :=
  Multicofork.IsColimit.desc hc f (fun _ => hf _)

@[reassoc (attr := simp)]
/--
lemma `π_desc` / 引理 `π_desc`

English:
lemma π_desc
  statement: (hc : IsColimit c) {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X)
  proof: by
  apply IsColimit.fac

中文:
引理 π_desc
  结论: (hc : IsColimit c) {X : C} (f : 对任意 j, (F.obj (op j)).obj j ⟶ X)
  证明: by
  apply IsColimit.fac

Depends on / 依赖: IsColimit, IsColimit.fac
-/
lemma π_desc (hc : IsColimit c) {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X)
    (hf : forall ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j) (j : J) :
    c.π j ≫ desc hc f hf = f j := by
  apply IsColimit.fac

end IsColimit

end Cowedge

section End

/--
Definition of `HasEnd` / `HasEnd` 的定义

English:
abbreviation HasEnd
  body: HasMultiequalizer (multicospanIndexEnd F)

中文:
缩写 HasEnd
  定义体: HasMultiequalizer (multicospanIndexEnd F)

Depends on / 依赖: HasMultiequalizer, multicospanIndexEnd
-/
abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)

variable [HasEnd F]

/--
Definition of `end_` / `end_` 的定义

English:
definition end_
  signature: : C
  body: multiequalizer (multicospanIndexEnd F)

中文:
定义 end_
  签名: : C
  定义体: multiequalizer (multicospanIndexEnd F)

Depends on / 依赖: multicospanIndexEnd, multiequalizer
-/
noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)

/--
Definition of `end_.π` / `end_.π` 的定义

English:
definition end_.π
  signature: (j : J)
  body: Multiequalizer.ι _ _

@[reassoc]

中文:
定义 end_.π
  签名: (j : J)
  定义体: Multiequalizer.ι _ _

@[reassoc]

Depends on / 依赖: Multiequalizer
-/
noncomputable def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _

@[reassoc]
/--
lemma `end_.condition` / 引理 `end_.condition`

English:
lemma end_.condition
  given: {i j : J} (f : i ⟶ j)
  proof: by
  apply Wedge.condition

中文:
引理 end_.condition
  条件: {i j : J} (f : i ⟶ j)
  证明: by
  apply Wedge.condition

Depends on / 依赖: Wedge.condition, condition
-/
lemma end_.condition {i j : J} (f : i ⟶ j) :
    π F i ≫ (F.obj (op i)).map f = π F j ≫ (F.map f.op).app j := by
  apply Wedge.condition

variable {F}

@[ext]
/--
lemma `end_.hom_ext` / 引理 `end_.hom_ext`

English:
lemma end_.hom_ext
  given: {X : C} {f g : X ⟶ end_ F} (h : forall j, f ≫ end_.π F j = g ≫ end_.π F j)
  proof: Multiequalizer.hom_ext _ _ _ (fun _ => h _)

中文:
引理 end_.hom_ext
  条件: {X : C} {f g : X ⟶ end_ F} (h : 对任意 j, f ≫ end_.π F j = g ≫ end_.π F j)
  证明: Multiequalizer.hom_ext _ _ _ (fun _ => h _)

Depends on / 依赖: Multiequalizer, Multiequalizer.hom_ext, hom_ext
-/
lemma end_.hom_ext {X : C} {f g : X ⟶ end_ F} (h : forall j, f ≫ end_.π F j = g ≫ end_.π F j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun _ => h _)

section

variable {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j)
  (hf : forall ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/--
Definition of `end_.lift` / `end_.lift` 的定义

English:
definition end_.lift
  signature: : X ⟶ end_ F
  body: Wedge.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]

中文:
定义 end_.lift
  签名: : X ⟶ end_ F
  定义体: Wedge.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, Wedge.IsLimit.lift, isLimit, limit.isLimit
-/
noncomputable def end_.lift : X ⟶ end_ F :=
  Wedge.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]
/--
lemma `end_.lift_π` / 引理 `end_.lift_π`

English:
lemma end_.lift_π
  given: (j : J)
  statement: lift f hf ≫ π F j = f j
  proof: by
  apply IsLimit.fac

中文:
引理 end_.lift_π
  条件: (j : J)
  结论: lift f hf ≫ π F j = f j
  证明: by
  apply IsLimit.fac

Depends on / 依赖: IsLimit, IsLimit.fac
-/
lemma end_.lift_π (j : J) : lift f hf ≫ π F j = f j := by
  apply IsLimit.fac

variable {F' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F'] (f : F ⟶ F')

/--
Definition of `end_.map` / `end_.map` 的定义

English:
definition end_.map
  signature: : end_ F ⟶ end_ F'
  body: end_.lift (fun x => end_.π _ _ ≫ (f.app (op x)).app x) (fun j j' φ => by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e]; rw [reassoc_of% end_.condition F φ]
    simp)

@[reassoc (attr := simp)]

中文:
定义 end_.map
  签名: : end_ F ⟶ end_ F'
  定义体: end_.lift (fun x => end_.π _ _ ≫ (f.app (op x)).app x) (fun j j' φ => by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e]; rw [reassoc_of% end_.condition F φ]
    simp)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, condition, end_, end_.condition, end_.lift, f.app, naturality, reassoc_of
-/
noncomputable def end_.map : end_ F ⟶ end_ F' :=
  end_.lift (fun x => end_.π _ _ ≫ (f.app (op x)).app x) (fun j j' φ => by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e]; rw [reassoc_of% end_.condition F φ]
    simp)

@[reassoc (attr := simp)]
/--
lemma `end_.map_π` / 引理 `end_.map_π`

English:
lemma end_.map_π
  given: (j : J)
  proof: by
  simp [end_.map]

@[reassoc (attr := simp)]

中文:
引理 end_.map_π
  条件: (j : J)
  证明: by
  simp [end_.map]

@[reassoc (attr := simp)]

Depends on / 依赖: end_, end_.map
-/
lemma end_.map_π (j : J) :
    end_.map f ≫ end_.π F' j = end_.π _ _ ≫ (f.app (op j)).app j := by
  simp [end_.map]

@[reassoc (attr := simp)]
/--
lemma `end_.map_comp` / 引理 `end_.map_comp`

English:
lemma end_.map_comp
  given: {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F''] (g : F' ⟶ F'')
  proof: by
  cat_disch

@[simp]

中文:
引理 end_.map_comp
  条件: {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F''] (g : F' ⟶ F'')
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma end_.map_comp {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F''] (g : F' ⟶ F'') :
    end_.map f ≫ end_.map g = end_.map (f ≫ g) := by
  cat_disch

@[simp]
/--
lemma `end_.map_id` / 引理 `end_.map_id`

English:
lemma end_.map_id
  statement: end_.map (𝟙 F) = 𝟙 _
  proof: by cat_disch

中文:
引理 end_.map_id
  结论: end_.map (𝟙 F) = 𝟙 _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma end_.map_id : end_.map (𝟙 F) = 𝟙 _ := by cat_disch

end

variable (J C) in
/-- If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have an end, then the construction
`F ↦ end_ F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`. -/
@[simps]
/--
Definition of `endFunctor` / `endFunctor` 的定义

English:
definition endFunctor
  signature: [forall (F : Jᵒᵖ ⥤ J ⥤ C), HasEnd F]
  body: end_ F
  map f := end_.map f

中文:
定义 endFunctor
  签名: [对任意 (F : Jᵒᵖ ⥤ J ⥤ C), HasEnd F]
  定义体: end_ F
  map f := end_.map f

Depends on / 依赖: end_
-/
noncomputable def endFunctor [forall (F : Jᵒᵖ ⥤ J ⥤ C), HasEnd F] :
    (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := end_ F
  map f := end_.map f

end End

section Coend

/--
Definition of `HasCoend` / `HasCoend` 的定义

English:
abbreviation HasCoend
  body: HasMulticoequalizer (multispanIndexCoend F)

中文:
缩写 HasCoend
  定义体: HasMulticoequalizer (multispanIndexCoend F)

Depends on / 依赖: HasMulticoequalizer, multispanIndexCoend
-/
abbrev HasCoend := HasMulticoequalizer (multispanIndexCoend F)

variable [HasCoend F]

/--
Definition of `coend` / `coend` 的定义

English:
definition coend
  signature: : C
  body: multicoequalizer (multispanIndexCoend F)

中文:
定义 coend
  签名: : C
  定义体: multicoequalizer (multispanIndexCoend F)

Depends on / 依赖: multicoequalizer, multispanIndexCoend
-/
noncomputable def coend : C := multicoequalizer (multispanIndexCoend F)

/--
Definition of `coend.ι` / `coend.ι` 的定义

English:
definition coend.ι
  signature: (j : J)
  body: Multicoequalizer.π (multispanIndexCoend F) _

@[reassoc]

中文:
定义 coend.ι
  签名: (j : J)
  定义体: Multicoequalizer.π (multispanIndexCoend F) _

@[reassoc]

Depends on / 依赖: Multicoequalizer, multispanIndexCoend
-/
noncomputable def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F :=
  Multicoequalizer.π (multispanIndexCoend F) _

@[reassoc]
/--
lemma `coend.condition` / 引理 `coend.condition`

English:
lemma coend.condition
  given: {i j : J} (f : i ⟶ j)
  proof: by
  apply Cowedge.condition

中文:
引理 coend.condition
  条件: {i j : J} (f : i ⟶ j)
  证明: by
  apply Cowedge.condition

Depends on / 依赖: Cowedge, Cowedge.condition, condition
-/
lemma coend.condition {i j : J} (f : i ⟶ j) :
     (F.map f.op).app i ≫ ι F i = (F.obj (op j)).map f ≫ ι F j := by
  apply Cowedge.condition

variable {F}

@[ext]
/--
lemma `coend.hom_ext` / 引理 `coend.hom_ext`

English:
lemma coend.hom_ext
  given: {X : C} {f g : coend F ⟶ X} (h : forall j, coend.ι F j ≫ f = coend.ι F j ≫ g)
  proof: Multicoequalizer.hom_ext _ _ _ (fun _ => h _)

中文:
引理 coend.hom_ext
  条件: {X : C} {f g : coend F ⟶ X} (h : 对任意 j, coend.ι F j ≫ f = coend.ι F j ≫ g)
  证明: Multicoequalizer.hom_ext _ _ _ (fun _ => h _)

Depends on / 依赖: Multicoequalizer, Multicoequalizer.hom_ext, hom_ext
-/
lemma coend.hom_ext {X : C} {f g : coend F ⟶ X} (h : forall j, coend.ι F j ≫ f = coend.ι F j ≫ g) :
    f = g :=
  Multicoequalizer.hom_ext _ _ _ (fun _ => h _)

section

variable {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X)
  (hf : forall ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/--
Definition of `coend.desc` / `coend.desc` 的定义

English:
definition coend.desc
  signature: : coend F ⟶ X
  body: Cowedge.IsColimit.desc (colimit.isColimit _) f hf

@[reassoc (attr := simp)]

中文:
定义 coend.desc
  签名: : coend F ⟶ X
  定义体: Cowedge.IsColimit.desc (colimit.isColimit _) f hf

@[reassoc (attr := simp)]

Depends on / 依赖: Cowedge, Cowedge.IsColimit.desc, IsColimit, colimit, colimit.isColimit, isColimit
-/
noncomputable def coend.desc : coend F ⟶ X :=
  Cowedge.IsColimit.desc (colimit.isColimit _) f hf

@[reassoc (attr := simp)]
/--
lemma `coend.ι_desc` / 引理 `coend.ι_desc`

English:
lemma coend.ι_desc
  given: (j : J)
  statement: ι F j ≫ desc f hf = f j
  proof: by
  apply IsColimit.fac

中文:
引理 coend.ι_desc
  条件: (j : J)
  结论: ι F j ≫ desc f hf = f j
  证明: by
  apply IsColimit.fac

Depends on / 依赖: IsColimit, IsColimit.fac
-/
lemma coend.ι_desc (j : J) : ι F j ≫ desc f hf = f j := by
  apply IsColimit.fac

variable {F' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F'] (f : F ⟶ F')

/--
Definition of `coend.map` / `coend.map` 的定义

English:
definition coend.map
  signature: : coend F ⟶ coend F'
  body: coend.desc (fun x => (f.app (op x)).app x ≫ coend.ι _ _) (fun j j' φ => by
    simp [coend.condition])

@[reassoc (attr := simp)]

中文:
定义 coend.map
  签名: : coend F ⟶ coend F'
  定义体: coend.desc (fun x => (f.app (op x)).app x ≫ coend.ι _ _) (fun j j' φ => by
    simp [coend.condition])

@[reassoc (attr := simp)]

Depends on / 依赖: coend.condition, coend.desc, condition, f.app
-/
noncomputable def coend.map : coend F ⟶ coend F' :=
  coend.desc (fun x => (f.app (op x)).app x ≫ coend.ι _ _) (fun j j' φ => by
    simp [coend.condition])

@[reassoc (attr := simp)]
/--
lemma `coend.ι_map` / 引理 `coend.ι_map`

English:
lemma coend.ι_map
  given: (j : J)
  proof: by
  simp [coend.map]

@[reassoc (attr := simp)]

中文:
引理 coend.ι_map
  条件: (j : J)
  证明: by
  simp [coend.map]

@[reassoc (attr := simp)]

Depends on / 依赖: coend.map
-/
lemma coend.ι_map (j : J) :
    coend.ι _ _ ≫ coend.map f = (f.app (op j)).app j ≫ coend.ι _ _ := by
  simp [coend.map]

@[reassoc (attr := simp)]
/--
lemma `coend.map_comp` / 引理 `coend.map_comp`

English:
lemma coend.map_comp
  given: {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F''] (g : F' ⟶ F'')
  proof: by
  cat_disch

@[simp]

中文:
引理 coend.map_comp
  条件: {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F''] (g : F' ⟶ F'')
  证明: by
  cat_disch

@[simp]

Depends on / 依赖: cat_disch
-/
lemma coend.map_comp {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F''] (g : F' ⟶ F'') :
    coend.map f ≫ coend.map g = coend.map (f ≫ g) := by
  cat_disch

@[simp]
/--
lemma `coend.map_id` / 引理 `coend.map_id`

English:
lemma coend.map_id
  statement: coend.map (𝟙 F) = 𝟙 _
  proof: by cat_disch

中文:
引理 coend.map_id
  结论: coend.map (𝟙 F) = 𝟙 _
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma coend.map_id : coend.map (𝟙 F) = 𝟙 _ := by cat_disch

end

variable (J C) in
/-- If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have a coend, then the construction
`F ↦ coend F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`. -/
@[simps]
/--
Definition of `coendFunctor` / `coendFunctor` 的定义

English:
definition coendFunctor
  signature: [forall (F : Jᵒᵖ ⥤ J ⥤ C), HasCoend F]
  body: coend F
  map f := coend.map f

中文:
定义 coendFunctor
  签名: [对任意 (F : Jᵒᵖ ⥤ J ⥤ C), HasCoend F]
  定义体: coend F
  map f := coend.map f
-/
noncomputable def coendFunctor [forall (F : Jᵒᵖ ⥤ J ⥤ C), HasCoend F] :
    (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := coend F
  map f := coend.map f

end Coend

end Limits

end CategoryTheory
