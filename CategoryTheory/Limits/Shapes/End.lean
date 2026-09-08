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
/-
**CategoryTheory.Limits.multicospanShapeEnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：multicospanShapeEnd : MulticospanShape where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of multiequalizer diagrams involved in the definition of ends.
-/
def multicospanShapeEnd : MulticospanShape where
  L := J
  R := Arrow J
  fst f := f.left
  snd f := f.right

variable (J) in
/-- The shape of multicoequalizer diagrams involved in the definition of coends. -/
@[simps]
/-
**CategoryTheory.Limits.multispanShapeCoend** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：multispanShapeCoend : MultispanShape where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shape of multicoequalizer diagrams involved in the definition of coends.
-/
def multispanShapeCoend : MultispanShape where
  L := Arrow J
  R := J
  fst f := f.left
  snd f := f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multicospan index which shall be used
to define the end of `F`. -/
@[simps]
/-
**CategoryTheory.Limits.multicospanIndexEnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：multicospanIndexEnd : MulticospanIndex (multicospanShapeEnd J) C where lef
t j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multicospan index which shall be used
to define the end of `F`.
-/
def multicospanIndexEnd : MulticospanIndex (multicospanShapeEnd J) C where
  left j := (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multispan used to define the coend
of `F`. -/
@[simps]
/-
**CategoryTheory.Limits.multispanIndexCoend** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：multispanIndexCoend : MultispanIndex (multispanShapeCoend J) C where left 
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multispan used to define the coend
of `F`.
-/
def multispanIndexCoend : MultispanIndex (multispanShapeCoend J) C where
  left f := (F.obj (op f.right)).obj f.left
  right j := (F.obj (op j)).obj j
  fst f := (F.map f.hom.op).app f.left
  snd f := (F.obj (op f.right)).map f.hom

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, a wedge for `F` is a type of cones (specifically
the type of multiforks for `multicospanIndexEnd F`):
the point of universal of these wedges shall be the end of `F`. -/
/-
**CategoryTheory.Limits.Wedge** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：Wedge
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, a wedge for `F` is a type of cones (specifically
the type of multiforks for `multicospanIndexEnd F`):
the point of universal of these wedges shall be the end of `F`.
-/
abbrev Wedge := Multifork (multicospanIndexEnd F)

namespace Wedge

variable {F}

/-- A variant of `CategoryTheory.Limits.Cone.ext` specialized to produce
isomorphisms of wedges. -/
@[simps!]
/-
**CategoryTheory.Limits.Wedge.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Wedge`。
形式化陈述：ext {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt) (he : forall j : J, W₁.ι j = e.h
om ≫ W₂.ι j
参数：e : W₁.pt ≅ W₂.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `CategoryTheory.Limits.Cone.ext` specialized to produce
isomorphisms of wedges.
-/
def ext {W₁ W₂ : Wedge F} (e : W₁.pt ≅ W₂.pt)
    (he : ∀ j : J, W₁.ι j = e.hom ≫ W₂.ι j := by cat_disch) : W₁ ≅ W₂ :=
  Cone.ext e (fun j =>
    match j with
    | .left _ => he _
    | .right f => by simpa using! (he f.left) =≫ _)

section Constructor

variable (pt : C) (π : ∀ (j : J), pt ⟶ (F.obj (op j)).obj j)
  (hπ : ∀ ⦃i j : J⦄ (f : i ⟶ j), π i ≫ (F.obj (op i)).map f = π j ≫ (F.map f.op).app j)

/-- Constructor for wedges. -/
/-
**CategoryTheory.Limits.Wedge.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its.Wedge`。
形式化陈述：mk : Wedge F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for wedges.
-/
abbrev mk : Wedge F :=
  Multifork.ofι _ pt π (fun f ↦ hπ f.hom)

@[simp]
/-
**CategoryTheory.Limits.Wedge.mk_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limi
ts.Wedge`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_ι (j : J) : (mk pt π hπ).ι j = π j := rfl

end Constructor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Limits.Wedge.condition** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Limits.Wedge`。
形式化陈述：condition (c : Wedge F) {i j : J} (f : i ⟶ j) : c.ι i ≫ (F.obj (op i)).map
 f = c.ι j ≫ (F.map f.op).app j
参数：c : Wedge F；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multifork.condition`：condition (b) : K.ι (J.fst b)
 ≫ I.fst b = K.ι (J.snd b) ≫ I.snd b

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma condition (c : Wedge F) {i j : J} (f : i ⟶ j) :
    c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j :=
  Multifork.condition c (Arrow.mk f)

namespace IsLimit

variable {c : Wedge F} (hc : IsLimit c)

/-
**CategoryTheory.Limits.Wedge.IsLimit.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits.Wedge.IsLimit`。
形式化陈述：hom_ext (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : forall j, f ≫ c.ι j
 = g ≫ c.ι j) : f = g
参数：hc : IsLimit c；h : forall j, f ≫ c.ι j = g ≫ c.ι j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multifork.IsLimit.hom_ext`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MulticospanShape}  
 {I : CategoryTheory.Limits.Multicosp…
-/
lemma hom_ext (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : ∀ j, f ≫ c.ι j = g ≫ c.ι j) :
    f = g :=
  Multifork.IsLimit.hom_ext hc h

/-- Construct a morphism to the end from its universal property. -/
/-
**CategoryTheory.Limits.Wedge.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Wedge.IsLimit`。
形式化陈述：lift (hc : IsLimit c) {X : C} (f : forall j, X ⟶ (F.obj (op j)).obj j) (hf
 : forall ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op)
.app j) : X ⟶ c.pt
参数：hc : IsLimit c；f : forall j, X ⟶ (F.obj (op j)).obj j；hf : forall ⦃i j : J⦄ (
g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism to the end from its universal property.
-/
def lift (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) :
    X ⟶ c.pt :=
  Multifork.IsLimit.lift hc f (fun _ ↦ hf _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Wedge.IsLimit.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Limits.Wedge.IsLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_ι (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) (j : J) :
    lift hc f hf ≫ c.ι j = f j := by
  apply IsLimit.fac


end IsLimit

end Wedge

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, a cowedge for `F` is a type of cocones
(specifically the type of multicoforks for `multispanIndexCoend F`):
the point of a universal cowedge is the coend of `F`. -/
/-
**CategoryTheory.Limits.Cowedge** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：Cowedge
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, a cowedge for `F` is a type of cocones
(specifically the type of multicoforks for `multispanIndexCoend F`):
the point of a universal cowedge is the coend of `F`.
-/
abbrev Cowedge := Multicofork (multispanIndexCoend F)

namespace Cowedge

variable {F}

set_option backward.isDefEq.respectTransparency.types false in
/-- A variant of `CategoryTheory.Limits.Cocone.ext` specialized to produce
isomorphisms of cowedges. -/
@[simps!]
/-
**CategoryTheory.Limits.Cowedge.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Cowedge`。
形式化陈述：ext {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt) (he : forall j : J, W₁.π j ≫ e
.hom = W₂.π j
参数：e : W₁.pt ≅ W₂.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `CategoryTheory.Limits.Cocone.ext` specialized to produce
isomorphisms of cowedges.
-/
def ext {W₁ W₂ : Cowedge F} (e : W₁.pt ≅ W₂.pt)
    (he : ∀ j : J, W₁.π j ≫ e.hom = W₂.π j := by cat_disch) : W₁ ≅ W₂ :=
  Cocone.ext e (fun j =>
    match j with
    | .right _ => he _
    | .left f => by simpa using! _ ≫= (he f.left))

section Constructor

variable (pt : C) (ι : ∀ (j : J), (F.obj (op j)).obj j ⟶ pt)
  (hι : ∀ ⦃i j : J⦄ (f : i ⟶ j), (F.map f.op).app i ≫ ι i = (F.obj (op j)).map f ≫ ι j)

/-- Constructor for cowedges. -/
/-
**CategoryTheory.Limits.Cowedge.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits.Cowedge`。
形式化陈述：mk : Cowedge F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cowedges.
-/
abbrev mk : Cowedge F :=
  Multicofork.ofπ _ pt ι (fun f ↦ hι f.hom)

@[simp]
/-
**CategoryTheory.Limits.Cowedge.mk_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Li
mits.Cowedge`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_π (j : J) : (mk pt ι hι).π j = ι j := rfl

end Constructor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Limits.Cowedge.condition** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits.Cowedge`。
形式化陈述：condition (c : Cowedge F) {i j : J} (f : i ⟶ j) : (F.map f.op).app i ≫ c.π
 i = (F.obj (op j)).map f ≫ c.π j
参数：c : Cowedge F；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicofork.condition`：condition (a) : I.fst a ≫ K
.π (J.fst a) = I.snd a ≫ K.π (J.snd a)

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma condition (c : Cowedge F) {i j : J} (f : i ⟶ j) :
    (F.map f.op).app i ≫ c.π i = (F.obj (op j)).map f ≫ c.π j :=
  Multicofork.condition c (Arrow.mk f)

namespace IsColimit

variable {c : Cowedge F} (hc : IsColimit c)

/-
**CategoryTheory.Limits.Cowedge.IsColimit.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits.Cowedge.IsColimit`。
形式化陈述：hom_ext (hc : IsColimit c) {X : C} {f g : c.pt ⟶ X} (h : forall j, c.π j ≫
 f = c.π j ≫ g) : f = g
参数：hc : IsColimit c；h : forall j, c.π j ≫ f = c.π j ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicofork.IsColimit.hom_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Limits.MultispanShape}
   {I : CategoryTheory.Limits.MultispanIn…
-/
lemma hom_ext (hc : IsColimit c) {X : C} {f g : c.pt ⟶ X} (h : ∀ j, c.π j ≫ f = c.π j ≫ g) :
    f = g :=
  Multicofork.IsColimit.hom_ext hc h

/-- Construct a morphism from the coend using its universal property. -/
/-
**CategoryTheory.Limits.Cowedge.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cowedge.IsColimit`。
形式化陈述：desc (hc : IsColimit c) {X : C} (f : forall j, (F.obj (op j)).obj j ⟶ X) (
hf : forall ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map
 g ≫ f j) : c.pt ⟶ X
参数：hc : IsColimit c；f : forall j, (F.obj (op j)).obj j ⟶ X；hf : forall ⦃i j : J⦄
 (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism from the coend using its universal property.
-/
def desc (hc : IsColimit c) {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j) :
    c.pt ⟶ X :=
  Multicofork.IsColimit.desc hc f (fun _ ↦ hf _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Cowedge.IsColimit.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits.Cowedge.IsColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_desc (hc : IsColimit c) {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j) (j : J) :
    c.π j ≫ desc hc f hf = f j := by
  apply IsColimit.fac

end IsColimit

end Cowedge

section End

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the end of `F`. -/
/-
**CategoryTheory.Limits.HasEnd** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：HasEnd
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the end of `F`.
-/
abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)

variable [HasEnd F]

/-- The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`. -/
/-
**CategoryTheory.Limits.end_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：end_ : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`.
-/
noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `end_ F ⟶ (F.obj (op j)).obj j`
for any `j : J`. -/
/-
**CategoryTheory.Limits.end_.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `end_ F ⟶ (F.obj (op j)).obj j`
for any `j : J`.
-/
noncomputable def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _

@[reassoc]
/-
**CategoryTheory.Limits.end_.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.end_`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   (F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)) [inst_2 : CategoryTheory.Limits.HasEnd F] {i j : J}  
 (f : i ⟶ j),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.end_.π
 F i) ((F.obj (Opposite.op i)).map f) =     CategoryTheory.CategoryStruct.comp (
CategoryTheory.Limits.end_.π F j) ((F.map f.op).app j)
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)；f : i ⟶ j；Categor
yTheory.Limits.end_.π F i；(F.obj (Opposite.op i)).map f；CategoryTheory.Limits.en
d_.π F j；(F.map f.op).app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Wedge.condition`：condition (c : Wedge F) {i j : J}
 (f : i ⟶ j) : c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j
-/
lemma end_.condition {i j : J} (f : i ⟶ j) :
    π F i ≫ (F.obj (op i)).map f = π F j ≫ (F.map f.op).app j := by
  apply Wedge.condition

variable {F}

@[ext]
/-
**CategoryTheory.Limits.end_.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.end_`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)} [inst_2 : CategoryTheory.Limits.HasEnd F] {X : C}   {
f g : X ⟶ CategoryTheory.Limits.end_ F},   (∀ (j : J),       CategoryTheory.Cate
goryStruct.comp f (CategoryTheory.Limits.end_.π F j) =         CategoryTheory.Ca
tegoryStruct.comp g (CategoryTheory.Limits.end_.π F j)) →     f = g
参数：CategoryTheory.Functor J C；∀ (j : J),       CategoryTheory.CategoryStruct.com
p f (CategoryTheory.Limits.end_.π F j) =         CategoryTheory.CategoryStruct.c
omp g (CategoryTheory.Limits.end_.π F j)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multiequalizer.hom_ext`：hom_ext {W : C} (i j : W ⟶
 multiequalizer I) (h : forall a, i ≫ Multiequalizer.ι I a = j ≫ Multiequalizer.
ι I a) : i = j
-/
lemma end_.hom_ext {X : C} {f g : X ⟶ end_ F} (h : ∀ j, f ≫ end_.π F j = g ≫ end_.π F j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun _ ↦ h _)

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/-- Constructor for morphisms to the end of a functor. -/
/-
**CategoryTheory.Limits.end_.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.end_`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {C : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} C] →         {F : Catego
ryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 : Categor
yTheory.Limits.HasEnd F] →             {X : C} →               (f : (j : J) → X 
⟶ (F.obj (Opposite.op j)).obj j) →                 (∀ ⦃i j : J⦄ (g : i ⟶ j),    
                 CategoryTheory.CategoryStruct.comp (f i) ((F.obj (Opposite.op i
)).map g) =                       CategoryTheory.CategoryStruct.comp (f j) ((F.m
ap g.op).app j)) →                   (X ⟶ CategoryTheory.Limits.end_ F)
参数：CategoryTheory.Functor J C；f : (j : J) → X ⟶ (F.obj (Opposite.op j)).obj j；∀ 
⦃i j : J⦄ (g : i ⟶ j),                     CategoryTheory.CategoryStruct.comp (f
 i) ((F.obj (Opposite.op i)).map g) =                       CategoryTheory.Categ
oryStruct.comp (f j) ((F.map g.op).app j)；X ⟶ CategoryTheory.Limits.end_ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to the end of a functor.
-/
noncomputable def end_.lift : X ⟶ end_ F :=
  Wedge.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.end_.lift_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma end_.lift_π (j : J) : lift f hf ≫ π F j = f j := by
  apply IsLimit.fac

variable {F' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F'] (f : F ⟶ F')

/-- A natural transformation of functors F ⟶ F' induces a map end_ F ⟶ end_ F'. -/
/-
**CategoryTheory.Limits.end_.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.end_`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {C : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} C] →         {F : Catego
ryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 : Categor
yTheory.Limits.HasEnd F] →             {F' : CategoryTheory.Functor Jᵒᵖ (Categor
yTheory.Functor J C)} →               [inst_3 : CategoryTheory.Limits.HasEnd F']
 →                 (F ⟶ F') → (CategoryTheory.Limits.end_ F ⟶ CategoryTheory.Lim
its.end_ F')
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；F ⟶ F'；CategoryTheory.L
imits.end_ F ⟶ CategoryTheory.Limits.end_ F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation of functors F ⟶ F' induces a map end_ F ⟶ end_ F'.
-/
noncomputable def end_.map : end_ F ⟶ end_ F' :=
  end_.lift (fun x ↦ end_.π _ _ ≫ (f.app (op x)).app x) (fun j j' φ ↦ by
    have e := (f.app (op j)).naturality φ
    simp only [Category.assoc]
    rw [← e, reassoc_of% end_.condition F φ]
    simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.end_.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limi
ts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma end_.map_π (j : J) :
    end_.map f ≫ end_.π F' j = end_.π _ _ ≫ (f.app (op j)).app j := by
  simp [end_.map]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.end_.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.end_`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)} [inst_2 : CategoryTheory.Limits.HasEnd F]   {F' : Cat
egoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} [inst_3 : CategoryTheory.L
imits.HasEnd F'] (f : F ⟶ F')   {F'' : CategoryTheory.Functor Jᵒᵖ (CategoryTheor
y.Functor J C)} [inst_4 : CategoryTheory.Limits.HasEnd F'']   (g : F' ⟶ F''),   
CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.end_.map f) (CategoryT
heory.Limits.end_.map g) =     CategoryTheory.Limits.end_.map (CategoryTheory.Ca
tegoryStruct.comp f g)
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；f : F ⟶ F'；CategoryTheo
ry.Functor J C；g : F' ⟶ F''；CategoryTheory.Limits.end_.map f；CategoryTheory.Limi
ts.end_.map g；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.end_.map_π`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]  
 {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.end_.map_π_assoc`：∀ {J : Type u} [inst : CategoryT
heory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'
} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma end_.map_comp {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasEnd F''] (g : F' ⟶ F'') :
    end_.map f ≫ end_.map g = end_.map (f ≫ g) := by
  cat_disch

@[simp]
/-
**CategoryTheory.Limits.end_.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits.end_`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)} [inst_2 : CategoryTheory.Limits.HasEnd F],   Category
Theory.Limits.end_.map (CategoryTheory.CategoryStruct.id F) =     CategoryTheory
.CategoryStruct.id (CategoryTheory.Limits.end_ F)
参数：CategoryTheory.Functor J C；CategoryTheory.CategoryStruct.id F；CategoryTheory.
Limits.end_ F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.end_.hom_ext`：∀ {J : Type u} [inst : CategoryTheor
y.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]
   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.end_.map_π`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C]  
 {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma end_.map_id : end_.map (𝟙 F) = 𝟙 _ := by cat_disch

end

variable (J C) in
/-- If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have an end, then the construction
`F ↦ end_ F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Limits.endFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：endFunctor [forall (F : Jᵒᵖ ⥤ J ⥤ C), HasEnd F] : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where 
obj F
参数：F : Jᵒᵖ ⥤ J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have an end, then the construction
`F ↦ end_ F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`.
-/
noncomputable def endFunctor [∀ (F : Jᵒᵖ ⥤ J ⥤ C), HasEnd F] :
    (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := end_ F
  map f := end_.map f

end End

section Coend

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the coend of `F`. -/
/-
**CategoryTheory.Limits.HasCoend** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：HasCoend
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the coend of `F`
.
-/
abbrev HasCoend := HasMulticoequalizer (multispanIndexCoend F)

variable [HasCoend F]

/-- The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`. -/
/-
**CategoryTheory.Limits.coend** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：coend : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`.
-/
noncomputable def coend : C := multicoequalizer (multispanIndexCoend F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the inclusion `(F.obj (op j)).obj j ⟶ coend F`
for any `j : J`. -/
/-
**CategoryTheory.Limits.coend.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the inclusion `(F.obj (op j)).obj j ⟶ coend F`
for any `j : J`.
-/
noncomputable def coend.ι (j : J) : (F.obj (op j)).obj j ⟶ coend F :=
  Multicoequalizer.π (multispanIndexCoend F) _

@[reassoc]
/-
**CategoryTheory.Limits.coend.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.coend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   (F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)) [inst_2 : CategoryTheory.Limits.HasCoend F] {i j : J}
   (f : i ⟶ j),   CategoryTheory.CategoryStruct.comp ((F.map f.op).app i) (Categ
oryTheory.Limits.coend.ι F i) =     CategoryTheory.CategoryStruct.comp ((F.obj (
Opposite.op j)).map f) (CategoryTheory.Limits.coend.ι F j)
参数：F : CategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)；f : i ⟶ j；(F.map 
f.op).app i；CategoryTheory.Limits.coend.ι F i；(F.obj (Opposite.op j)).map f；Cate
goryTheory.Limits.coend.ι F j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.Cowedge.condition`：condition (c : Cowedge F) {i j 
: J} (f : i ⟶ j) : (F.map f.op).app i ≫ c.π i = (F.obj (op j)).map f ≫ c.π j
-/
lemma coend.condition {i j : J} (f : i ⟶ j) :
     (F.map f.op).app i ≫ ι F i = (F.obj (op j)).map f ≫ ι F j := by
  apply Cowedge.condition

variable {F}

@[ext]
/-
**CategoryTheory.Limits.coend.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.coend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)} [inst_2 : CategoryTheory.Limits.HasCoend F] {X : C}  
 {f g : CategoryTheory.Limits.coend F ⟶ X},   (∀ (j : J),       CategoryTheory.C
ategoryStruct.comp (CategoryTheory.Limits.coend.ι F j) f =         CategoryTheor
y.CategoryStruct.comp (CategoryTheory.Limits.coend.ι F j) g) →     f = g
参数：CategoryTheory.Functor J C；∀ (j : J),       CategoryTheory.CategoryStruct.com
p (CategoryTheory.Limits.coend.ι F j) f =         CategoryTheory.CategoryStruct.
comp (CategoryTheory.Limits.coend.ι F j) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.hom_ext`：hom_ext {W : C} (i j : m
ulticoequalizer I ⟶ W) (h : forall b, Multicoequalizer.π I b ≫ i = Multicoequali
zer.π I b ≫ j) : i = j
-/
lemma coend.hom_ext {X : C} {f g : coend F ⟶ X} (h : ∀ j, coend.ι F j ≫ f = coend.ι F j ≫ g) :
    f = g :=
  Multicoequalizer.hom_ext _ _ _ (fun _ ↦ h _)

section

variable {X : C} (f : ∀ j, (F.obj (op j)).obj j ⟶ X)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), (F.map g.op).app i ≫ f i = (F.obj (op j)).map g ≫ f j)

/-- Constructor for morphisms to the coend of a functor. -/
/-
**CategoryTheory.Limits.coend.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.coend`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {C : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} C] →         {F : Catego
ryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 : Categor
yTheory.Limits.HasCoend F] →             {X : C} →               (f : (j : J) → 
(F.obj (Opposite.op j)).obj j ⟶ X) →                 (∀ ⦃i j : J⦄ (g : i ⟶ j),  
                   CategoryTheory.CategoryStruct.comp ((F.map g.op).app i) (f i)
 =                       CategoryTheory.CategoryStruct.comp ((F.obj (Opposite.op
 j)).map g) (f j)) →                   (CategoryTheory.Limits.coend F ⟶ X)
参数：CategoryTheory.Functor J C；f : (j : J) → (F.obj (Opposite.op j)).obj j ⟶ X；∀ 
⦃i j : J⦄ (g : i ⟶ j),                     CategoryTheory.CategoryStruct.comp ((
F.map g.op).app i) (f i) =                       CategoryTheory.CategoryStruct.c
omp ((F.obj (Opposite.op j)).map g) (f j)；CategoryTheory.Limits.coend F ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to the coend of a functor.
-/
noncomputable def coend.desc : coend F ⟶ X :=
  Cowedge.IsColimit.desc (colimit.isColimit _) f hf

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coend.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coend.ι_desc (j : J) : ι F j ≫ desc f hf = f j := by
  apply IsColimit.fac

variable {F' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F'] (f : F ⟶ F')

/-- A natural transformation of functors F ⟶ F' induces a map coend F ⟶ coend F'. -/
/-
**CategoryTheory.Limits.coend.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.coend`。
形式化陈述：{J : Type u} →   [inst : CategoryTheory.Category.{v, u} J] →     {C : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} C] →         {F : Catego
ryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} →           [inst_2 : Categor
yTheory.Limits.HasCoend F] →             {F' : CategoryTheory.Functor Jᵒᵖ (Categ
oryTheory.Functor J C)} →               [inst_3 : CategoryTheory.Limits.HasCoend
 F'] →                 (F ⟶ F') → (CategoryTheory.Limits.coend F ⟶ CategoryTheor
y.Limits.coend F')
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；F ⟶ F'；CategoryTheory.L
imits.coend F ⟶ CategoryTheory.Limits.coend F'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation of functors F ⟶ F' induces a map coend F ⟶ coend F'.
-/
noncomputable def coend.map : coend F ⟶ coend F' :=
  coend.desc (fun x ↦ (f.app (op x)).app x ≫ coend.ι _ _) (fun j j' φ ↦ by
    simp [coend.condition])

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coend.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coend.ι_map (j : J) :
    coend.ι _ _ ≫ coend.map f = (f.app (op j)).app j ≫ coend.ι _ _ := by
  simp [coend.map]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coend.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)} [inst_2 : CategoryTheory.Limits.HasCoend F]   {F' : C
ategoryTheory.Functor Jᵒᵖ (CategoryTheory.Functor J C)} [inst_3 : CategoryTheory
.Limits.HasCoend F']   (f : F ⟶ F') {F'' : CategoryTheory.Functor Jᵒᵖ (CategoryT
heory.Functor J C)}   [inst_4 : CategoryTheory.Limits.HasCoend F''] (g : F' ⟶ F'
'),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.coend.map f) (Ca
tegoryTheory.Limits.coend.map g) =     CategoryTheory.Limits.coend.map (Category
Theory.CategoryStruct.comp f g)
参数：CategoryTheory.Functor J C；CategoryTheory.Functor J C；f : F ⟶ F'；CategoryTheo
ry.Functor J C；g : F' ⟶ F''；CategoryTheory.Limits.coend.map f；CategoryTheory.Lim
its.coend.map g；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coend.hom_ext`：∀ {J : Type u} [inst : CategoryTheo
ry.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coend.ι_map_assoc`：∀ {J : Type u} [inst : Category
Theory.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u
'} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.coend.ι_map`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coend.map_comp {F'' : Jᵒᵖ ⥤ J ⥤ C} [HasCoend F''] (g : F' ⟶ F'') :
    coend.map f ≫ coend.map g = coend.map (f ≫ g) := by
  cat_disch

@[simp]
/-
**CategoryTheory.Limits.coend.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.coend`。
形式化陈述：∀ {J : Type u} [inst : CategoryTheory.Category.{v, u} J] {C : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} C]   {F : CategoryTheory.Functor Jᵒᵖ (Ca
tegoryTheory.Functor J C)} [inst_2 : CategoryTheory.Limits.HasCoend F],   Catego
ryTheory.Limits.coend.map (CategoryTheory.CategoryStruct.id F) =     CategoryThe
ory.CategoryStruct.id (CategoryTheory.Limits.coend F)
参数：CategoryTheory.Functor J C；CategoryTheory.CategoryStruct.id F；CategoryTheory.
Limits.coend F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coend.hom_ext`：∀ {J : Type u} [inst : CategoryTheo
ry.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F : CategoryTheory.F…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.coend.ι_map`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coend.map_id : coend.map (𝟙 F) = 𝟙 _ := by cat_disch

end

variable (J C) in
/-- If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have a coend, then the construction
`F ↦ coend F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`. -/
@[simps]
/-
**CategoryTheory.Limits.coendFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：coendFunctor [forall (F : Jᵒᵖ ⥤ J ⥤ C), HasCoend F] : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C wh
ere obj F
参数：F : Jᵒᵖ ⥤ J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all bifunctors `Jᵒᵖ ⥤ J ⥤ C` have a coend, then the construction
`F ↦ coend F` defines a functor `(Jᵒᵖ ⥤ J ⥤ C) ⥤ C`.
-/
noncomputable def coendFunctor [∀ (F : Jᵒᵖ ⥤ J ⥤ C), HasCoend F] :
    (Jᵒᵖ ⥤ J ⥤ C) ⥤ C where
  obj F := coend F
  map f := coend.map f

end Coend

end Limits

end CategoryTheory

