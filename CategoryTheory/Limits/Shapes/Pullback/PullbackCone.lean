/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel, Bhavik Mehta, Andrew Yang, Emily Riehl, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# PullbackCone

This file provides API for interacting with cones (resp. cocones) in the case of pullbacks
(resp. pushouts).

## Main definitions

* `PullbackCone f g`: Given morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, a term `t : PullbackCone f g`
  provides the data of a cone pictured as follows
  ```
  t.pt ---t.snd---> Y
    |               |
  t.fst            g
    |               |
    v               v
    X -----f------> Z
  ```
  The type `PullbackCone f g` is implemented as an abbreviation for `Cone (cospan f g)`, so general
  results about cones are also available for `PullbackCone f g`.

* `PushoutCone f g`: Given morphisms `f : X ⟶ Y` and `g : X ⟶ Z`, a term `t : PushoutCone f g`
  provides the data of a cocone pictured as follows
  ```
    X -----f------> Y
    |               |
    g               t.inr
    |               |
    v               v
    Z ---t.inl---> t.pt
  ```
  Similar to `PullbackCone`, `PushoutCone f g` is implemented as an abbreviation for
  `Cocone (span f g)`, so general results about cocones are also available for `PushoutCone f g`.

## API
We summarize the most important parts of the API for pullback cones here. The dual notions for
pushout cones are also available in this file.

Various ways of constructing pullback cones:
* `PullbackCone.mk` constructs a term of `PullbackCone f g` given morphisms `fst` and `snd` such
  that `fst ≫ f = snd ≫ g`.
* `PullbackCone.flip` is the `PullbackCone` obtained by flipping `fst` and `snd`.

Interaction with `IsLimit`:
* `PullbackCone.isLimitAux` and `PullbackCone.isLimitAux'` provide two convenient ways to show that
  a given `PullbackCone` is a limit cone.
* `PullbackCone.isLimit.mk` provides a convenient way to show that a `PullbackCone` constructed
  using `PullbackCone.mk` is a limit cone.
* `PullbackCone.IsLimit.lift` and `PullbackCone.IsLimit.lift'` provides convenient ways for
  constructing the morphisms to the point of a limit `PullbackCone` from the universal property.
* `PullbackCone.IsLimit.hom_ext` provides a convenient way to show that two morphisms to the point
  of a limit `PullbackCone` are equal.

Interaction with `CommSq`:
* `CommSq.cone` and `CommSq.cocone` provide the implicit (non-limiting) pullback cone and pushout
  cocone associated with a commuting square

## References
* [Stacks: Fibre products](https://stacks.math.columbia.edu/tag/001U)
* [Stacks: Pushouts](https://stacks.math.columbia.edu/tag/0025)
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

/-- A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z` and
`g : Y ⟶ Z`. -/
/-
**CategoryTheory.Limits.PullbackCone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z)
参数：f : X ⟶ Z；g : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pullback cone is just a cone on the cospan formed by two morphisms `f : X ⟶ Z`
 and
`g : Y ⟶ Z`.
-/
abbrev PullbackCone (f : X ⟶ Z) (g : Y ⟶ Z) :=
  Cone (cospan f g)

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The first projection of a pullback cone. -/
/-
**CategoryTheory.Limits.PullbackCone.fst** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits.PullbackCone`。
形式化陈述：fst (t : PullbackCone f g) : t.pt ⟶ X
参数：t : PullbackCone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection of a pullback cone.
-/
abbrev fst (t : PullbackCone f g) : t.pt ⟶ X :=
  t.π.app WalkingCospan.left

/-- The second projection of a pullback cone. -/
/-
**CategoryTheory.Limits.PullbackCone.snd** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits.PullbackCone`。
形式化陈述：snd (t : PullbackCone f g) : t.pt ⟶ Y
参数：t : PullbackCone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection of a pullback cone.
-/
abbrev snd (t : PullbackCone f g) : t.pt ⟶ Y :=
  t.π.app WalkingCospan.right
/-
**CategoryTheory.Limits.PullbackCone.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.PullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_app_left (c : PullbackCone f g) : c.π.app WalkingCospan.left = c.fst := rfl
/-
**CategoryTheory.Limits.PullbackCone.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.PullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_app_right (c : PullbackCone f g) : c.π.app WalkingCospan.right = c.snd := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.PullbackCone.condition_one** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫
 f
参数：t : PullbackCone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem condition_one (t : PullbackCone f g) : t.π.app WalkingCospan.one = t.fst ≫ f := by
  have w := t.π.naturality WalkingCospan.Hom.inl
  dsimp at w; simpa using w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd : W ⟶ Y`
such that `fst ≫ f = snd ≫ g`. -/
@[simps]
/-
**CategoryTheory.Limits.PullbackCone.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.PullbackCone`。
形式化陈述：mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g
参数：fst : W ⟶ X；snd : W ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pullback cone on `f` and `g` is determined by morphisms `fst : W ⟶ X` and `snd
 : W ⟶ Y`
such that `fst ≫ f = snd ≫ g`.
-/
def mk {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g := by cat_disch) :
    PullbackCone f g where
  pt := W
  π := { app := fun j => Option.casesOn j (fst ≫ f) fun j' => WalkingPair.casesOn j' fst snd
         naturality := by rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) j <;> cases j <;> simp [eq] }

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.mk_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.PullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_π_app_left {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.left = fst := rfl

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.mk_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.PullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_π_app_right {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.right = snd := rfl

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.mk_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.PullbackCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_π_app_one {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).π.app WalkingCospan.one = fst ≫ f := rfl

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.mk_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.PullbackCone`。
形式化陈述：mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk 
fst snd eq).fst = fst
参数：fst : W ⟶ X；snd : W ⟶ Y；eq : fst ≫ f = snd ≫ g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_fst {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).fst = fst := rfl

@[simp]
/-
**CategoryTheory.Limits.PullbackCone.mk_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.PullbackCone`。
形式化陈述：mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) : (mk 
fst snd eq).snd = snd
参数：fst : W ⟶ X；snd : W ⟶ Y；eq : fst ≫ f = snd ≫ g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_snd {W : C} (fst : W ⟶ X) (snd : W ⟶ Y) (eq : fst ≫ f = snd ≫ g) :
    (mk fst snd eq).snd = snd := rfl

@[reassoc]
/-
**CategoryTheory.Limits.PullbackCone.condition** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.PullbackCone`。
形式化陈述：condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g
参数：t : PullbackCone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem condition (t : PullbackCone f g) : fst t ≫ f = snd t ≫ g :=
  (t.w inl).trans (t.w inr).symm

set_option backward.isDefEq.respectTransparency false in
/-- To check whether two morphisms are equalized by the maps of a pullback cone, it suffices to
check it for `fst t` and `snd t` -/
/-
**CategoryTheory.Limits.PullbackCone.equalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   (t : CategoryTheory.Limits.PullbackCone f g) {W : C} {k l :
 W ⟶ t.pt},   CategoryTheory.CategoryStruct.comp k t.fst = CategoryTheory.Catego
ryStruct.comp l t.fst →     CategoryTheory.CategoryStruct.comp k t.snd = Categor
yTheory.CategoryStruct.comp l t.snd →       ∀ (j : CategoryTheory.Limits.Walking
Cospan),         CategoryTheory.CategoryStruct.comp k (t.π.app j) = CategoryTheo
ry.CategoryStruct.comp l (t.π.app j)
参数：t : CategoryTheory.Limits.PullbackCone f g；j : CategoryTheory.Limits.WalkingC
ospan；t.π.app j；t.π.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h

--- 原说明 ---
To check whether two morphisms are equalized by the maps of a pullback cone, it 
suffices to
check it for `fst t` and `snd t`
-/
theorem equalizer_ext (t : PullbackCone f g) {W : C} {k l : W ⟶ t.pt} (h₀ : k ≫ fst t = l ≫ fst t)
    (h₁ : k ≫ snd t = l ≫ snd t) : ∀ j : WalkingCospan, k ≫ t.π.app j = l ≫ t.π.app j
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w inl, reassoc_of% h₀]

/-- To construct an isomorphism of pullback cones, it suffices to construct an isomorphism
of the cone points and check it commutes with `fst` and `snd`. -/
/-
**CategoryTheory.Limits.PullbackCone.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.PullbackCone`。
形式化陈述：ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst
参数：i : s.pt ≅ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of pullback cones, it suffices to construct an isomo
rphism
of the cone points and check it commutes with `fst` and `snd`.
-/
def ext {s t : PullbackCone f g} (i : s.pt ≅ t.pt) (w₁ : s.fst = i.hom ≫ t.fst := by cat_disch)
    (w₂ : s.snd = i.hom ≫ t.snd := by cat_disch) : s ≅ t :=
  WalkingCospan.ext i w₁ w₂

set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between a pullback cone and the corresponding pullback cone
reconstructed using `PullbackCone.mk`. -/
@[simps!]
/-
**CategoryTheory.Limits.PullbackCone.eta** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.PullbackCone`。
形式化陈述：eta (t : PullbackCone f g) : t ≅ mk t.fst t.snd t.condition
参数：t : PullbackCone f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
The natural isomorphism between a pullback cone and the corresponding pullback c
one
reconstructed using `PullbackCone.mk`.
-/
def eta (t : PullbackCone f g) : t ≅ mk t.fst t.snd t.condition :=
  PullbackCone.ext (Iso.refl _)

/-- This is a slightly more convenient method to verify that a pullback cone is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitAux** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.PullbackCone`。
形式化陈述：isLimitAux (t : PullbackCone f g) (lift : forall s : PullbackCone f g, s.p
t ⟶ t.pt) (fac_left : forall s : PullbackCone f g, lift s ≫ t.fst = s.fst) (fac_
right : forall s : PullbackCone f g, lift s ≫ t.snd = s.snd) (uniq : forall (s :
 PullbackCone f g) (m : s.pt ⟶ t.pt) (_ : forall j : WalkingCospan, m ≫ t.π.app 
j = s.π.app j), m = lift s) : IsLimit t
参数：t : PullbackCone f g；lift : forall s : PullbackCone f g, s.pt ⟶ t.pt；fac_left
 : forall s : PullbackCone f g, lift s ≫ t.fst = s.fst；fac_right : forall s : Pu
llbackCone f g, lift s ≫ t.snd = s.snd；uniq : forall (s : PullbackCone f g) (m :
 s.pt ⟶ t.pt) (_ : forall j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lif
t s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a pullback cone is a li
mit cone. It
only asks for a proof of facts that carry any mathematical content
-/
def isLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd)
    (uniq : ∀ (s : PullbackCone f g) (m : s.pt ⟶ t.pt)
      (_ : ∀ j : WalkingCospan, m ≫ t.π.app j = s.π.app j), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w inl, ← t.w inl, ← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/-- This is another convenient method to verify that a pullback cone is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitAux'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.PullbackCone`。
形式化陈述：isLimitAux' (t : PullbackCone f g) (create : forall s : PullbackCone f g, 
{ l // l ≫ t.fst = s.fst ∧ l ≫ t.snd = s.snd ∧ forall {m}, m ≫ t.fst = s.fst -> 
m ≫ t.snd = s.snd -> m = l }) : Limits.IsLimit t
参数：t : PullbackCone f g；create : forall s : PullbackCone f g, { l // l ≫ t.fst =
 s.fst ∧ l ≫ t.snd = s.snd ∧ forall {m}, m ≫ t.fst = s.fst -> m ≫ t.snd = s.snd 
-> m = l }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a pullback cone is a limit cone
. It
only asks for a proof of facts that carry any mathematical content, and allows a
ccess to the
same `s` for all parts.
-/
def isLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd ∧ ∀ {m}, m ≫ t.fst = s.fst → m ≫ t.snd = s.snd → m = l }) :
    Limits.IsLimit t :=
  PullbackCone.isLimitAux t (fun s => (create s).1) (fun s => (create s).2.1)
    (fun s => (create s).2.2.1) fun s _ w =>
    (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a limit cone.
-/
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           {W : C} →             {
fst : W ⟶ X} →               {snd : W ⟶ Y} →                 (eq : CategoryTheor
y.CategoryStruct.comp fst f = CategoryTheory.CategoryStruct.comp snd g) →       
            (lift : (s : CategoryTheory.Limits.PullbackCone f g) → s.pt ⟶ W) →  
                   (∀ (s : CategoryTheory.Limits.PullbackCone f g),             
            CategoryTheory.CategoryStruct.comp (lift s) fst = s.fst) →          
             (∀ (s : CategoryTheory.Limits.PullbackCone f g),                   
        CategoryTheory.CategoryStruct.comp (lift s) snd = s.snd) →              
           (∀ (s : CategoryTheory.Limits.PullbackCone f g) (m : s.pt ⟶ W),      
                       CategoryTheory.CategoryStruct.comp m fst = s.fst →       
                        CategoryTheory.CategoryStruct.comp m snd = s.snd → m = l
ift s) →                           CategoryTheory.Limits.IsLimit (CategoryTheory
.Limits.PullbackCone.mk fst snd eq)
参数：eq : CategoryTheory.CategoryStruct.comp fst f = CategoryTheory.CategoryStruct
.comp snd g；lift : (s : CategoryTheory.Limits.PullbackCone f g) → s.pt ⟶ W；∀ (s 
: CategoryTheory.Limits.PullbackCone f g),                         CategoryTheor
y.CategoryStruct.comp (lift s) fst = s.fst；∀ (s : CategoryTheory.Limits.Pullback
Cone f g),                           CategoryTheory.CategoryStruct.comp (lift s)
 snd = s.snd；∀ (s : CategoryTheory.Limits.PullbackCone f g) (m : s.pt ⟶ W),     
                        CategoryTheory.CategoryStruct.comp m fst = s.fst →      
                         CategoryTheory.CategoryStruct.comp m snd = s.snd → m = 
lift s；CategoryTheory.Limits.PullbackCone.mk fst snd eq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `PullbackCone` constructed 
using
`PullbackCone.mk` is a limit cone.
-/
def IsLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd)
    (uniq :
      ∀ (s : PullbackCone f g) (m : s.pt ⟶ W) (_ : m ≫ fst = s.fst) (_ : m ≫ snd = s.snd),
        m = lift s) :
    IsLimit (mk fst snd eq) :=
  isLimitAux _ lift fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   {t : CategoryTheory.Limits.PullbackCone f g} (ht : Category
Theory.Limits.IsLimit t) {W : C} {k l : W ⟶ t.pt},   CategoryTheory.CategoryStru
ct.comp k t.fst = CategoryTheory.CategoryStruct.comp l t.fst →     CategoryTheor
y.CategoryStruct.comp k t.snd = CategoryTheory.CategoryStruct.comp l t.snd → k =
 l
参数：ht : CategoryTheory.Limits.IsLimit t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Limits.PullbackCone.equalizer_ext`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : Ca
tegoryTheory.Limits.PullbackCone f g) …
-/
theorem IsLimit.hom_ext {t : PullbackCone f g} (ht : IsLimit t) {W : C} {k l : W ⟶ t.pt}
    (h₀ : k ≫ fst t = l ≫ fst t) (h₁ : k ≫ snd t = l ≫ snd t) : k = l :=
  ht.hom_ext <| equalizer_ext _ h₀ h₁

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
`h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
and `l ≫ snd t = k`, see `IsLimit.lift_fst` and `IsLimit.lift_snd`. -/
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           {t : CategoryTheory.Lim
its.PullbackCone f g} →             CategoryTheory.Limits.IsLimit t →           
    {W : C} →                 (h : W ⟶ X) →                   (k : W ⟶ Y) →     
                CategoryTheory.CategoryStruct.comp h f = CategoryTheory.Category
Struct.comp k g → (W ⟶ t.pt)
参数：h : W ⟶ X；k : W ⟶ Y；W ⟶ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y`
 are such that
`h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
and `l ≫ snd t = k`, see `IsLimit.lift_fst` and `IsLimit.lift_snd`.
-/
def IsLimit.lift {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
  ht.lift <| PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   {t : CategoryTheory.Limits.PullbackCone f g} (ht : Category
Theory.Limits.IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)   (w : CategoryTheory.C
ategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g),   CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.Limits.PullbackCone.IsLimit.lift ht h k w
) t.fst = h
参数：ht : CategoryTheory.Limits.IsLimit t；h : W ⟶ X；k : W ⟶ Y；w : CategoryTheory.C
ategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g；CategoryTheory.L
imits.PullbackCone.IsLimit.lift ht h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma IsLimit.lift_fst {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ fst t = h := ht.fac _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   {t : CategoryTheory.Limits.PullbackCone f g} (ht : Category
Theory.Limits.IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)   (w : CategoryTheory.C
ategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g),   CategoryTheo
ry.CategoryStruct.comp (CategoryTheory.Limits.PullbackCone.IsLimit.lift ht h k w
) t.snd = k
参数：ht : CategoryTheory.Limits.IsLimit t；h : W ⟶ X；k : W ⟶ Y；w : CategoryTheory.C
ategoryStruct.comp h f = CategoryTheory.CategoryStruct.comp k g；CategoryTheory.L
imits.PullbackCone.IsLimit.lift ht h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma IsLimit.lift_snd {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : IsLimit.lift ht h k w ≫ snd t = k := ht.fac _ _

/-- If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such that
`h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
-/
/-
**CategoryTheory.Limits.PullbackCone.IsLimit.lift'** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Z} →         {g : Y ⟶ Z} →           {t : CategoryTheory.Lim
its.PullbackCone f g} →             CategoryTheory.Limits.IsLimit t →           
    {W : C} →                 (h : W ⟶ X) →                   (k : W ⟶ Y) →     
                CategoryTheory.CategoryStruct.comp h f = CategoryTheory.Category
Struct.comp k g →                       { l //                         CategoryT
heory.CategoryStruct.comp l t.fst = h ∧                           CategoryTheory
.CategoryStruct.comp l t.snd = k }
参数：h : W ⟶ X；k : W ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is a limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y`
 are such that
`h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫
 snd t = k`.
-/
def IsLimit.lift' {t : PullbackCone f g} (ht : IsLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : { l : W ⟶ t.pt // l ≫ fst t = h ∧ l ≫ snd t = k } :=
  ⟨IsLimit.lift ht h k w, by simp⟩

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
limit, is also a limit. -/
/-
**CategoryTheory.Limits.PullbackCone.mkSelfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：mkSelfIsLimit {t : PullbackCone f g} (ht : IsLimit t) : IsLimit (mk t.fst 
t.snd t.condition)
参数：ht : IsLimit t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone tha
t is a
limit, is also a limit.
-/
def mkSelfIsLimit {t : PullbackCone f g} (ht : IsLimit t) : IsLimit (mk t.fst t.snd t.condition) :=
  IsLimit.ofIsoLimit ht (eta t)

section Flip

variable (t : PullbackCone f g)

/-- The pullback cone obtained by flipping `fst` and `snd`. -/
/-
**CategoryTheory.Limits.PullbackCone.flip** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.PullbackCone`。
形式化陈述：flip : PullbackCone g f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback cone obtained by flipping `fst` and `snd`.
-/
def flip : PullbackCone g f := PullbackCone.mk _ _ t.condition.symm
/-
**CategoryTheory.Limits.PullbackCone.flip_pt** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   (t : CategoryTheory.Limits.PullbackCone f g), t.flip.pt = t
.pt
参数：t : CategoryTheory.Limits.PullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_pt : t.flip.pt = t.pt := rfl
/-
**CategoryTheory.Limits.PullbackCone.flip_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   (t : CategoryTheory.Limits.PullbackCone f g), t.flip.fst = 
t.snd
参数：t : CategoryTheory.Limits.PullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_fst : t.flip.fst = t.snd := rfl
/-
**CategoryTheory.Limits.PullbackCone.flip_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.PullbackCone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Z} {g : Y ⟶ Z}   (t : CategoryTheory.Limits.PullbackCone f g), t.flip.snd = 
t.fst
参数：t : CategoryTheory.Limits.PullbackCone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_snd : t.flip.snd = t.fst := rfl

/-- Flipping a pullback cone twice gives an isomorphic cone. -/
/-
**CategoryTheory.Limits.PullbackCone.flipFlipIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.PullbackCone`。
形式化陈述：flipFlipIso : t.flip.flip ≅ t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flipping a pullback cone twice gives an isomorphic cone.
-/
def flipFlipIso : t.flip.flip ≅ t := PullbackCone.ext (Iso.refl _) (by simp) (by simp)

variable {t}

set_option backward.isDefEq.respectTransparency false in
/-- The flip of a pullback square is a pullback square. -/
/-
**CategoryTheory.Limits.PullbackCone.flipIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.PullbackCone`。
形式化陈述：flipIsLimit (ht : IsLimit t) : IsLimit t.flip
参数：ht : IsLimit t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The flip of a pullback square is a pullback square.
-/
def flipIsLimit (ht : IsLimit t) : IsLimit t.flip :=
  IsLimit.mk _ (fun s => ht.lift s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsLimit.hom_ext ht <;> simp [h₁, h₂])

/-- A square is a pullback square if its flip is. -/
/-
**CategoryTheory.Limits.PullbackCone.isLimitOfFlip** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PullbackCone`。
形式化陈述：isLimitOfFlip (ht : IsLimit t.flip) : IsLimit t
参数：ht : IsLimit t.flip。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square is a pullback square if its flip is.
-/
def isLimitOfFlip (ht : IsLimit t.flip) : IsLimit t :=
  IsLimit.ofIsoLimit (flipIsLimit ht) t.flipFlipIso

end Flip

end PullbackCone

/-- This is a helper construction that can be useful when verifying that a category has all
pullbacks. Given `F : WalkingCospan ⥤ C`, which is really the same as
`cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map inr`, we
get a cone on `F`.

If you're thinking about using this, have a look at `hasPullbacks_of_hasLimit_cospan`,
which you may find to be an easier way of achieving your goal. -/
@[simps]
/-
**CategoryTheory.Limits.Cone.ofPullbackCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Cone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingCospan C} →       CategoryTheory
.Limits.PullbackCone (F.map CategoryTheory.Limits.WalkingCospan.Hom.inl)        
   (F.map CategoryTheory.Limits.WalkingCospan.Hom.inr) →         CategoryTheory.
Limits.Cone F
参数：F.map CategoryTheory.Limits.WalkingCospan.Hom.inl；F.map CategoryTheory.Limits
.WalkingCospan.Hom.inr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a helper construction that can be useful when verifying that a category 
has all
pullbacks. Given `F : WalkingCospan ⥤ C`, which is really the same as
`cospan (F.map inl) (F.map inr)`, and a pullback cone on `F.map inl` and `F.map 
inr`, we
get a cone on `F`.

If you're thinking about using this, have a look at `hasPullbacks_of_hasLimit_co
span`,
which you may find to be an easier way of achieving your goal.
-/
def Cone.ofPullbackCone {F : WalkingCospan ⥤ C} (t : PullbackCone (F.map inl) (F.map inr)) :
    Cone F where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).inv

/-- Given `F : WalkingCospan ⥤ C`, which is really the same as `cospan (F.map inl) (F.map inr)`,
and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`. -/
@[simps]
/-
**CategoryTheory.Limits.PullbackCone.ofCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.PullbackCone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingCospan C} →       CategoryTheory
.Limits.Cone F →         CategoryTheory.Limits.PullbackCone (F.map CategoryTheor
y.Limits.WalkingCospan.Hom.inl)           (F.map CategoryTheory.Limits.WalkingCo
span.Hom.inr)
参数：F.map CategoryTheory.Limits.WalkingCospan.Hom.inl；F.map CategoryTheory.Limits
.WalkingCospan.Hom.inr。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : WalkingCospan ⥤ C`, which is really the same as `cospan (F.map inl) (
F.map inr)`,
and a cone on `F`, we get a pullback cone on `F.map inl` and `F.map inr`.
-/
def PullbackCone.ofCone {F : WalkingCospan ⥤ C} (t : Cone F) :
    PullbackCone (F.map inl) (F.map inr) where
  pt := t.pt
  π := t.π ≫ (diagramIsoCospan F).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A diagram `WalkingCospan ⥤ C` is isomorphic to some `PullbackCone.mk` after
composing with `diagramIsoCospan`. -/
@[simps!]
/-
**CategoryTheory.Limits.PullbackCone.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.PullbackCone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingCospan C} →       (t : CategoryT
heory.Limits.Cone F) →         (CategoryTheory.Limits.Cone.postcompose (Category
Theory.Limits.diagramIsoCospan F).hom).obj t ≅           CategoryTheory.Limits.P
ullbackCone.mk (t.π.app CategoryTheory.Limits.WalkingCospan.left)             (t
.π.app CategoryTheory.Limits.WalkingCospan.right) ⋯
参数：t : CategoryTheory.Limits.Cone F；CategoryTheory.Limits.Cone.postcompose (Cate
goryTheory.Limits.diagramIsoCospan F).hom；t.π.app CategoryTheory.Limits.WalkingC
ospan.left；t.π.app CategoryTheory.Limits.WalkingCospan.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A diagram `WalkingCospan ⥤ C` is isomorphic to some `PullbackCone.mk` after
composing with `diagramIsoCospan`.
-/
def PullbackCone.isoMk {F : WalkingCospan ⥤ C} (t : Cone F) :
    (Cone.postcompose (diagramIsoCospan.{v} _).hom).obj t ≅
      PullbackCone.mk (t.π.app WalkingCospan.left) (t.π.app WalkingCospan.right)
        ((t.π.naturality inl).symm.trans (t.π.naturality inr :)) :=
  Cone.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;> simp

/-- A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y` and
`g : X ⟶ Z`. -/
/-
**CategoryTheory.Limits.PushoutCocone** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z)
参数：f : X ⟶ Y；g : X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pushout cocone is just a cocone on the span formed by two morphisms `f : X ⟶ Y
` and
`g : X ⟶ Z`.
-/
abbrev PushoutCocone (f : X ⟶ Y) (g : X ⟶ Z) :=
  Cocone (span f g)

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

/-- The first inclusion of a pushout cocone. -/
/-
**CategoryTheory.Limits.PushoutCocone.inl** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.PushoutCocone`。
形式化陈述：inl (t : PushoutCocone f g) : Y ⟶ t.pt
参数：t : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first inclusion of a pushout cocone.
-/
abbrev inl (t : PushoutCocone f g) : Y ⟶ t.pt :=
  t.ι.app WalkingSpan.left

/-- The second inclusion of a pushout cocone. -/
/-
**CategoryTheory.Limits.PushoutCocone.inr** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits.PushoutCocone`。
形式化陈述：inr (t : PushoutCocone f g) : Z ⟶ t.pt
参数：t : PushoutCocone f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second inclusion of a pushout cocone.
-/
abbrev inr (t : PushoutCocone f g) : Z ⟶ t.pt :=
  t.ι.app WalkingSpan.right

-- This cannot be `@[simp]` because `c.inl` is reducibly defeq to the LHS.
/-
**CategoryTheory.Limits.PushoutCocone.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.PushoutCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_app_left (c : PushoutCocone f g) : c.ι.app WalkingSpan.left = c.inl := rfl

-- This cannot be `@[simp]` because `c.inr` is reducibly defeq to the LHS.
/-
**CategoryTheory.Limits.PushoutCocone.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.PushoutCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_app_right (c : PushoutCocone f g) : c.ι.app WalkingSpan.right = c.inr := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.PushoutCocone.condition_zero** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PushoutCocone`。
形式化陈述：condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.
inl
参数：t : PushoutCocone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem condition_zero (t : PushoutCocone f g) : t.ι.app WalkingSpan.zero = f ≫ t.inl := by
  have w := t.ι.naturality WalkingSpan.Hom.fst
  dsimp at w; simpa using w.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `inr : Z ⟶ W` such
that `f ≫ inl = g ↠ inr`. -/
@[simps]
/-
**CategoryTheory.Limits.PushoutCocone.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.PushoutCocone`。
形式化陈述：mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutC
ocone f g where pt
参数：inl : Y ⟶ W；inr : Z ⟶ W；eq : f ≫ inl = g ≫ inr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pushout cocone on `f` and `g` is determined by morphisms `inl : Y ⟶ W` and `in
r : Z ⟶ W` such
that `f ≫ inl = g ↠ inr`.
-/
def mk {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : PushoutCocone f g where
  pt := W
  ι := { app := fun j => Option.casesOn j (f ≫ inl) fun j' => WalkingPair.casesOn j' inl inr
         naturality := by
          rintro (⟨⟩ | ⟨⟨⟩⟩) (⟨⟩ | ⟨⟨⟩⟩) <;> intro f <;> cases f <;> dsimp <;> aesop }

@[simp]
/-
**CategoryTheory.Limits.PushoutCocone.mk_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.PushoutCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_ι_app_left {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.left = inl := rfl

@[simp]
/-
**CategoryTheory.Limits.PushoutCocone.mk_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.PushoutCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_ι_app_right {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.right = inr := rfl

@[simp]
/-
**CategoryTheory.Limits.PushoutCocone.mk_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.PushoutCocone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_ι_app_zero {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).ι.app WalkingSpan.zero = f ≫ inl := rfl

@[simp]
/-
**CategoryTheory.Limits.PushoutCocone.mk_inl** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.PushoutCocone`。
形式化陈述：mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : (mk 
inl inr eq).inl = inl
参数：inl : Y ⟶ W；inr : Z ⟶ W；eq : f ≫ inl = g ≫ inr。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inl {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inl = inl := rfl

@[simp]
/-
**CategoryTheory.Limits.PushoutCocone.mk_inr** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.PushoutCocone`。
形式化陈述：mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) : (mk 
inl inr eq).inr = inr
参数：inl : Y ⟶ W；inr : Z ⟶ W；eq : f ≫ inl = g ≫ inr。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inr {W : C} (inl : Y ⟶ W) (inr : Z ⟶ W) (eq : f ≫ inl = g ≫ inr) :
    (mk inl inr eq).inr = inr := rfl

@[reassoc]
/-
**CategoryTheory.Limits.PushoutCocone.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.PushoutCocone`。
形式化陈述：condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t
参数：t : PushoutCocone f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem condition (t : PushoutCocone f g) : f ≫ inl t = g ≫ inr t :=
  (t.w fst).trans (t.w snd).symm

set_option backward.isDefEq.respectTransparency false in
/-- To check whether a morphism is coequalized by the maps of a pushout cocone, it suffices to check
  it for `inl t` and `inr t` -/
/-
**CategoryTheory.Limits.PushoutCocone.coequalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   (t : CategoryTheory.Limits.PushoutCocone f g) {W : C} {k l 
: t.pt ⟶ W},   CategoryTheory.CategoryStruct.comp t.inl k = CategoryTheory.Categ
oryStruct.comp t.inl l →     CategoryTheory.CategoryStruct.comp t.inr k = Catego
ryTheory.CategoryStruct.comp t.inr l →       ∀ (j : CategoryTheory.Limits.Walkin
gSpan),         CategoryTheory.CategoryStruct.comp (t.ι.app j) k = CategoryTheor
y.CategoryStruct.comp (t.ι.app j) l
参数：t : CategoryTheory.Limits.PushoutCocone f g；j : CategoryTheory.Limits.Walking
Span；t.ι.app j；t.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
To check whether a morphism is coequalized by the maps of a pushout cocone, it s
uffices to check
  it for `inl t` and `inr t`
-/
theorem coequalizer_ext (t : PushoutCocone f g) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) :
    ∀ j : WalkingSpan, t.ι.app j ≫ k = t.ι.app j ≫ l
  | some WalkingPair.left => h₀
  | some WalkingPair.right => h₁
  | none => by rw [← t.w fst, Category.assoc, Category.assoc, h₀]

/-- To construct an isomorphism of pushout cocones, it suffices to construct an isomorphism
of the cocone points and check it commutes with `inl` and `inr`. -/
/-
**CategoryTheory.Limits.PushoutCocone.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.PushoutCocone`。
形式化陈述：ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.in
l
参数：i : s.pt ≅ t.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism of pushout cocones, it suffices to construct an isom
orphism
of the cocone points and check it commutes with `inl` and `inr`.
-/
def ext {s t : PushoutCocone f g} (i : s.pt ≅ t.pt) (w₁ : s.inl ≫ i.hom = t.inl := by cat_disch)
    (w₂ : s.inr ≫ i.hom = t.inr := by cat_disch) : s ≅ t :=
  WalkingSpan.ext i w₁ w₂

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism between a pushout cocone and the corresponding pushout cocone
reconstructed using `PushoutCocone.mk`. -/
@[simps!]
/-
**CategoryTheory.Limits.PushoutCocone.eta** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits.PushoutCocone`。
形式化陈述：eta (t : PushoutCocone f g) : t ≅ mk t.inl t.inr t.condition
参数：t : PushoutCocone f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t

--- 原说明 ---
The natural isomorphism between a pushout cocone and the corresponding pushout c
ocone
reconstructed using `PushoutCocone.mk`.
-/
def eta (t : PushoutCocone f g) : t ≅ mk t.inl t.inr t.condition :=
  PushoutCocone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- This is a slightly more convenient method to verify that a pushout cocone is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitAux** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitAux (t : PushoutCocone f g) (desc : forall s : PushoutCocone f g,
 t.pt ⟶ s.pt) (fac_left : forall s : PushoutCocone f g, t.inl ≫ desc s = s.inl) 
(fac_right : forall s : PushoutCocone f g, t.inr ≫ desc s = s.inr) (uniq : foral
l (s : PushoutCocone f g) (m : t.pt ⟶ s.pt) (_ : forall j : WalkingSpan, t.ι.app
 j ≫ m = s.ι.app j), m = desc s) : IsColimit t
参数：t : PushoutCocone f g；desc : forall s : PushoutCocone f g, t.pt ⟶ s.pt；fac_le
ft : forall s : PushoutCocone f g, t.inl ≫ desc s = s.inl；fac_right : forall s :
 PushoutCocone f g, t.inr ≫ desc s = s.inr；uniq : forall (s : PushoutCocone f g)
 (m : t.pt ⟶ s.pt) (_ : forall j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = 
desc s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a pushout cocone is a c
olimit cocone.
It only asks for a proof of facts that carry any mathematical content
-/
def isColimitAux (t : PushoutCocone f g) (desc : ∀ s : PushoutCocone f g, t.pt ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, t.inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, t.inr ≫ desc s = s.inr)
    (uniq : ∀ (s : PushoutCocone f g) (m : t.pt ⟶ s.pt)
    (_ : ∀ j : WalkingSpan, t.ι.app j ≫ m = s.ι.app j), m = desc s) : IsColimit t :=
  { desc
    fac := fun s j =>
      Option.casesOn j (by simp [← s.w fst, ← t.w fst, fac_left s]) fun j' =>
        WalkingPair.casesOn j' (fac_left s) (fac_right s)
    uniq := uniq }

/-- This is another convenient method to verify that a pushout cocone is a colimit cocone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitAux'** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitAux' (t : PushoutCocone f g) (create : forall s : PushoutCocone f
 g, { l // t.inl ≫ l = s.inl ∧ t.inr ≫ l = s.inr ∧ forall {m}, t.inl ≫ m = s.inl
 -> t.inr ≫ m = s.inr -> m = l }) : IsColimit t
参数：t : PushoutCocone f g；create : forall s : PushoutCocone f g, { l // t.inl ≫ l
 = s.inl ∧ t.inr ≫ l = s.inr ∧ forall {m}, t.inl ≫ m = s.inl -> t.inr ≫ m = s.in
r -> m = l }。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a pushout cocone is a colimit c
ocone. It
only asks for a proof of facts that carry any mathematical content, and allows a
ccess to the
same `s` for all parts.
-/
def isColimitAux' (t : PushoutCocone f g)
    (create :
      ∀ s : PushoutCocone f g,
        { l //
          t.inl ≫ l = s.inl ∧
            t.inr ≫ l = s.inr ∧ ∀ {m}, t.inl ≫ m = s.inl → t.inr ≫ m = s.inr → m = l }) :
    IsColimit t :=
  isColimitAux t (fun s => (create s).1) (fun s => (create s).2.1) (fun s => (create s).2.2.1)
    fun s _ w => (create s).2.2.2 (w WalkingCospan.left) (w WalkingCospan.right)
/-
**CategoryTheory.Limits.PushoutCocone.IsColimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits.PushoutCocone.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   {t : CategoryTheory.Limits.PushoutCocone f g} (ht : Categor
yTheory.Limits.IsColimit t) {W : C} {k l : t.pt ⟶ W},   CategoryTheory.CategoryS
truct.comp t.inl k = CategoryTheory.CategoryStruct.comp t.inl l →     CategoryTh
eory.CategoryStruct.comp t.inr k = CategoryTheory.CategoryStruct.comp t.inr l → 
k = l
参数：ht : CategoryTheory.Limits.IsColimit t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.coequalizer_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (t :
 CategoryTheory.Limits.PushoutCocone f g)…
-/
theorem IsColimit.hom_ext {t : PushoutCocone f g} (ht : IsColimit t) {W : C} {k l : t.pt ⟶ W}
    (h₀ : inl t ≫ k = inl t ≫ l) (h₁ : inr t ≫ k = inr t ≫ l) : k = l :=
  ht.hom_ext <| coequalizer_ext _ h₀ h₁

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W` such that
`inl t ≫ l = h` and `inr t ≫ l = k`, see `IsColimit.inl_desc` and `IsColimit.inr_desc`. -/
/-
**CategoryTheory.Limits.PushoutCocone.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.PushoutCocone.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           {t : CategoryTheory.Lim
its.PushoutCocone f g} →             CategoryTheory.Limits.IsColimit t →        
       {W : C} →                 (h : Y ⟶ W) →                   (k : Z ⟶ W) →  
                   CategoryTheory.CategoryStruct.comp f h = CategoryTheory.Categ
oryStruct.comp g k → (t.pt ⟶ W)
参数：h : Y ⟶ W；k : Z ⟶ W；t.pt ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶
 W` are
morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W
` such that
`inl t ≫ l = h` and `inr t ≫ l = k`, see `IsColimit.inl_desc` and `IsColimit.inr
_desc`.
-/
def IsColimit.desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : t.pt ⟶ W :=
  ht.desc (PushoutCocone.mk _ _ w)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PushoutCocone.IsColimit.inl_desc** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.PushoutCocone.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   {t : CategoryTheory.Limits.PushoutCocone f g} (ht : Categor
yTheory.Limits.IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)   (w : CategoryTheor
y.CategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g k),   CategoryT
heory.CategoryStruct.comp t.inl (CategoryTheory.Limits.PushoutCocone.IsColimit.d
esc ht h k w) = h
参数：ht : CategoryTheory.Limits.IsColimit t；h : Y ⟶ W；k : Z ⟶ W；w : CategoryTheory
.CategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g k；CategoryTheory
.Limits.PushoutCocone.IsColimit.desc ht h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma IsColimit.inl_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inl t ≫ IsColimit.desc ht h k w = h :=
  ht.fac _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.PushoutCocone.IsColimit.inr_desc** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.PushoutCocone.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   {t : CategoryTheory.Limits.PushoutCocone f g} (ht : Categor
yTheory.Limits.IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)   (w : CategoryTheor
y.CategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g k),   CategoryT
heory.CategoryStruct.comp t.inr (CategoryTheory.Limits.PushoutCocone.IsColimit.d
esc ht h k w) = k
参数：ht : CategoryTheory.Limits.IsColimit t；h : Y ⟶ W；k : Z ⟶ W；w : CategoryTheory
.CategoryStruct.comp f h = CategoryTheory.CategoryStruct.comp g k；CategoryTheory
.Limits.PushoutCocone.IsColimit.desc ht h k w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma IsColimit.inr_desc {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : inr t ≫ IsColimit.desc ht h k w = k :=
  ht.fac _ _

/-- If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶ W` are
morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W` such that
`inl t ≫ l = h` and `inr t ≫ l = k`. -/
/-
**CategoryTheory.Limits.PushoutCocone.IsColimit.desc'** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.PushoutCocone.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           {t : CategoryTheory.Lim
its.PushoutCocone f g} →             CategoryTheory.Limits.IsColimit t →        
       {W : C} →                 (h : Y ⟶ W) →                   (k : Z ⟶ W) →  
                   CategoryTheory.CategoryStruct.comp f h = CategoryTheory.Categ
oryStruct.comp g k →                       { l //                         Catego
ryTheory.CategoryStruct.comp t.inl l = h ∧                           CategoryThe
ory.CategoryStruct.comp t.inr l = k }
参数：h : Y ⟶ W；k : Z ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `t` is a colimit pushout cocone over `f` and `g` and `h : Y ⟶ W` and `k : Z ⟶
 W` are
morphisms satisfying `f ≫ h = g ≫ k`, then we have a factorization `l : t.pt ⟶ W
` such that
`inl t ≫ l = h` and `inr t ≫ l = k`.
-/
def IsColimit.desc' {t : PushoutCocone f g} (ht : IsColimit t) {W : C} (h : Y ⟶ W) (k : Z ⟶ W)
    (w : f ≫ h = g ≫ k) : { l : t.pt ⟶ W // inl t ≫ l = h ∧ inr t ≫ l = k } :=
  ⟨IsColimit.desc ht h k w, by simp⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a more convenient formulation to show that a `PushoutCocone` constructed using
`PushoutCocone.mk` is a colimit cocone.
-/
/-
**CategoryTheory.Limits.PushoutCocone.IsColimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.PushoutCocone.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           {W : C} →             {
inl : Y ⟶ W} →               {inr : Z ⟶ W} →                 (eq : CategoryTheor
y.CategoryStruct.comp f inl = CategoryTheory.CategoryStruct.comp g inr) →       
            (desc : (s : CategoryTheory.Limits.PushoutCocone f g) → W ⟶ s.pt) → 
                    (∀ (s : CategoryTheory.Limits.PushoutCocone f g),           
              CategoryTheory.CategoryStruct.comp inl (desc s) = s.inl) →        
               (∀ (s : CategoryTheory.Limits.PushoutCocone f g),                
           CategoryTheory.CategoryStruct.comp inr (desc s) = s.inr) →           
              (∀ (s : CategoryTheory.Limits.PushoutCocone f g) (m : W ⟶ s.pt),  
                           CategoryTheory.CategoryStruct.comp inl m = s.inl →   
                            CategoryTheory.CategoryStruct.comp inr m = s.inr → m
 = desc s) →                           CategoryTheory.Limits.IsColimit (Category
Theory.Limits.PushoutCocone.mk inl inr eq)
参数：eq : CategoryTheory.CategoryStruct.comp f inl = CategoryTheory.CategoryStruct
.comp g inr；desc : (s : CategoryTheory.Limits.PushoutCocone f g) → W ⟶ s.pt；∀ (s
 : CategoryTheory.Limits.PushoutCocone f g),                         CategoryThe
ory.CategoryStruct.comp inl (desc s) = s.inl；∀ (s : CategoryTheory.Limits.Pushou
tCocone f g),                           CategoryTheory.CategoryStruct.comp inr (
desc s) = s.inr；∀ (s : CategoryTheory.Limits.PushoutCocone f g) (m : W ⟶ s.pt), 
                            CategoryTheory.CategoryStruct.comp inl m = s.inl →  
                             CategoryTheory.CategoryStruct.comp inr m = s.inr → 
m = desc s；CategoryTheory.Limits.PushoutCocone.mk inl inr eq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a more convenient formulation to show that a `PushoutCocone` constructed
 using
`PushoutCocone.mk` is a colimit cocone.
-/
def IsColimit.mk {W : C} {inl : Y ⟶ W} {inr : Z ⟶ W} (eq : f ≫ inl = g ≫ inr)
    (desc : ∀ s : PushoutCocone f g, W ⟶ s.pt)
    (fac_left : ∀ s : PushoutCocone f g, inl ≫ desc s = s.inl)
    (fac_right : ∀ s : PushoutCocone f g, inr ≫ desc s = s.inr)
    (uniq :
      ∀ (s : PushoutCocone f g) (m : W ⟶ s.pt) (_ : inl ≫ m = s.inl) (_ : inr ≫ m = s.inr),
        m = desc s) :
    IsColimit (mk inl inr eq) :=
  isColimitAux _ desc fac_left fac_right fun s m w =>
    uniq s m (w WalkingCospan.left) (w WalkingCospan.right)

/-- The pushout cocone reconstructed using `PushoutCocone.mk` from a pushout cocone that is a
colimit, is also a colimit. -/
/-
**CategoryTheory.Limits.PushoutCocone.mkSelfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.PushoutCocone`。
形式化陈述：mkSelfIsColimit {t : PushoutCocone f g} (ht : IsColimit t) : IsColimit (mk
 t.inl t.inr t.condition)
参数：ht : IsColimit t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t

--- 原说明 ---
The pushout cocone reconstructed using `PushoutCocone.mk` from a pushout cocone 
that is a
colimit, is also a colimit.
-/
def mkSelfIsColimit {t : PushoutCocone f g} (ht : IsColimit t) :
    IsColimit (mk t.inl t.inr t.condition) :=
  IsColimit.ofIsoColimit ht (eta t)

section Flip

variable (t : PushoutCocone f g)

/-- The pushout cocone obtained by flipping `inl` and `inr`. -/
/-
**CategoryTheory.Limits.PushoutCocone.flip** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.PushoutCocone`。
形式化陈述：flip : PushoutCocone g f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout cocone obtained by flipping `inl` and `inr`.
-/
def flip : PushoutCocone g f := PushoutCocone.mk _ _ t.condition.symm
/-
**CategoryTheory.Limits.PushoutCocone.flip_pt** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   (t : CategoryTheory.Limits.PushoutCocone f g), t.flip.pt = 
t.pt
参数：t : CategoryTheory.Limits.PushoutCocone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_pt : t.flip.pt = t.pt := rfl
/-
**CategoryTheory.Limits.PushoutCocone.flip_inl** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   (t : CategoryTheory.Limits.PushoutCocone f g), t.flip.inl =
 t.inr
参数：t : CategoryTheory.Limits.PushoutCocone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_inl : t.flip.inl = t.inr := rfl
/-
**CategoryTheory.Limits.PushoutCocone.flip_inr** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.PushoutCocone`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : 
X ⟶ Y} {g : X ⟶ Z}   (t : CategoryTheory.Limits.PushoutCocone f g), t.flip.inr =
 t.inl
参数：t : CategoryTheory.Limits.PushoutCocone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma flip_inr : t.flip.inr = t.inl := rfl

/-- Flipping a pushout cocone twice gives an isomorphic cocone. -/
/-
**CategoryTheory.Limits.PushoutCocone.flipFlipIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.PushoutCocone`。
形式化陈述：flipFlipIso : t.flip.flip ≅ t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flipping a pushout cocone twice gives an isomorphic cocone.
-/
def flipFlipIso : t.flip.flip ≅ t := PushoutCocone.ext (Iso.refl _) (by simp) (by simp)

variable {t}

set_option backward.isDefEq.respectTransparency false in
/-- The flip of a pushout square is a pushout square. -/
/-
**CategoryTheory.Limits.PushoutCocone.flipIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.PushoutCocone`。
形式化陈述：flipIsColimit (ht : IsColimit t) : IsColimit t.flip
参数：ht : IsColimit t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The flip of a pushout square is a pushout square.
-/
def flipIsColimit (ht : IsColimit t) : IsColimit t.flip :=
  IsColimit.mk _ (fun s => ht.desc s.flip) (by simp) (by simp) (fun s m h₁ h₂ => by
    apply IsColimit.hom_ext ht <;> simp [h₁, h₂])

/-- A square is a pushout square if its flip is. -/
/-
**CategoryTheory.Limits.PushoutCocone.isColimitOfFlip** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.PushoutCocone`。
形式化陈述：isColimitOfFlip (ht : IsColimit t.flip) : IsColimit t
参数：ht : IsColimit t.flip。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A square is a pushout square if its flip is.
-/
def isColimitOfFlip (ht : IsColimit t.flip) : IsColimit t :=
  IsColimit.ofIsoColimit (flipIsColimit ht) t.flipFlipIso

end Flip

end PushoutCocone

/-- This is a helper construction that can be useful when verifying that a category has all
pushout. Given `F : WalkingSpan ⥤ C`, which is really the same as
`span (F.map fst) (F.map snd)`, and a pushout cocone on `F.map fst` and `F.map snd`,
we get a cocone on `F`.

If you're thinking about using this, have a look at `hasPushouts_of_hasColimit_span`, which
you may find to be an easier way of achieving your goal. -/
@[simps]
/-
**CategoryTheory.Limits.Cocone.ofPushoutCocone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingSpan C} →       CategoryTheory.L
imits.PushoutCocone (F.map CategoryTheory.Limits.WalkingSpan.Hom.fst)           
(F.map CategoryTheory.Limits.WalkingSpan.Hom.snd) →         CategoryTheory.Limit
s.Cocone F
参数：F.map CategoryTheory.Limits.WalkingSpan.Hom.fst；F.map CategoryTheory.Limits.W
alkingSpan.Hom.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a helper construction that can be useful when verifying that a category 
has all
pushout. Given `F : WalkingSpan ⥤ C`, which is really the same as
`span (F.map fst) (F.map snd)`, and a pushout cocone on `F.map fst` and `F.map s
nd`,
we get a cocone on `F`.

If you're thinking about using this, have a look at `hasPushouts_of_hasColimit_s
pan`, which
you may find to be an easier way of achieving your goal.
-/
def Cocone.ofPushoutCocone {F : WalkingSpan ⥤ C} (t : PushoutCocone (F.map fst) (F.map snd)) :
    Cocone F where
  pt := t.pt
  ι := (diagramIsoSpan F).hom ≫ t.ι
/-- Given `F : WalkingSpan ⥤ C`, which is really the same as `span (F.map fst) (F.map snd)`,
and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`. -/
@[simps]
/-
**CategoryTheory.Limits.PushoutCocone.ofCocone** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PushoutCocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingSpan C} →       CategoryTheory.L
imits.Cocone F →         CategoryTheory.Limits.PushoutCocone (F.map CategoryTheo
ry.Limits.WalkingSpan.Hom.fst)           (F.map CategoryTheory.Limits.WalkingSpa
n.Hom.snd)
参数：F.map CategoryTheory.Limits.WalkingSpan.Hom.fst；F.map CategoryTheory.Limits.W
alkingSpan.Hom.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : WalkingSpan ⥤ C`, which is really the same as `span (F.map fst) (F.ma
p snd)`,
and a cocone on `F`, we get a pushout cocone on `F.map fst` and `F.map snd`.
-/
def PushoutCocone.ofCocone {F : WalkingSpan ⥤ C} (t : Cocone F) :
    PushoutCocone (F.map fst) (F.map snd) where
  pt := t.pt
  ι := (diagramIsoSpan F).inv ≫ t.ι

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A diagram `WalkingSpan ⥤ C` is isomorphic to some `PushoutCocone.mk` after composing with
`diagramIsoSpan`. -/
@[simps!]
/-
**CategoryTheory.Limits.PushoutCocone.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.PushoutCocone`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {F : Cate
goryTheory.Functor CategoryTheory.Limits.WalkingSpan C} →       (t : CategoryThe
ory.Limits.Cocone F) →         (CategoryTheory.Limits.Cocone.precompose (Categor
yTheory.Limits.diagramIsoSpan F).inv).obj t ≅           CategoryTheory.Limits.Pu
shoutCocone.mk (t.ι.app CategoryTheory.Limits.WalkingSpan.left)             (t.ι
.app CategoryTheory.Limits.WalkingSpan.right) ⋯
参数：t : CategoryTheory.Limits.Cocone F；CategoryTheory.Limits.Cocone.precompose (C
ategoryTheory.Limits.diagramIsoSpan F).inv；t.ι.app CategoryTheory.Limits.Walking
Span.left；t.ι.app CategoryTheory.Limits.WalkingSpan.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A diagram `WalkingSpan ⥤ C` is isomorphic to some `PushoutCocone.mk` after compo
sing with
`diagramIsoSpan`.
-/
def PushoutCocone.isoMk {F : WalkingSpan ⥤ C} (t : Cocone F) :
    (Cocone.precompose (diagramIsoSpan.{v} _).inv).obj t ≅
      PushoutCocone.mk (t.ι.app WalkingSpan.left) (t.ι.app WalkingSpan.right)
        ((t.ι.naturality fst).trans (t.ι.naturality snd).symm) :=
  Cocone.ext (Iso.refl _) <| by
    rintro (_ | (_ | _)) <;> simp

end Limits

namespace CommSq
open Limits
variable {C : Type*} [Category* C]

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- The (not necessarily limiting) `PullbackCone h i` implicit in the statement
that we have `CommSq f g h i`.
-/
/-
**CategoryTheory.CommSq.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : C} →       {f : W ⟶ X} →         {g : W ⟶ Y} → {h : X ⟶ Z} → {i : Y ⟶ Z}
 → CategoryTheory.CommSq f g h i → CategoryTheory.Limits.PullbackCone h i
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…

--- 原说明 ---
The (not necessarily limiting) `PullbackCone h i` implicit in the statement
that we have `CommSq f g h i`.
-/
def cone (s : CommSq f g h i) : PullbackCone h i :=
  PullbackCone.mk _ _ s.w

/-- The (not necessarily limiting) `PushoutCocone f g` implicit in the statement
that we have `CommSq f g h i`.
-/
/-
**CategoryTheory.CommSq.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommSq`
。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {W 
X Y Z : C} →       {f : W ⟶ X} →         {g : W ⟶ Y} →           {h : X ⟶ Z} → {
i : Y ⟶ Z} → CategoryTheory.CommSq f g h i → CategoryTheory.Limits.PushoutCocone
 f g
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…

--- 原说明 ---
The (not necessarily limiting) `PushoutCocone f g` implicit in the statement
that we have `CommSq f g h i`.
-/
def cocone (s : CommSq f g h i) : PushoutCocone f g :=
  PushoutCocone.mk _ _ s.w

@[simp]
/-
**CategoryTheory.CommSq.cone_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z} (s : CategoryTheory.CommSq 
f g h i), s.cone.fst = f
参数：s : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cone_fst (s : CommSq f g h i) : s.cone.fst = f :=
  rfl

@[simp]
/-
**CategoryTheory.CommSq.cone_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z} (s : CategoryTheory.CommSq 
f g h i), s.cone.snd = g
参数：s : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cone_snd (s : CommSq f g h i) : s.cone.snd = g :=
  rfl

@[simp]
/-
**CategoryTheory.CommSq.cocone_inl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z} (s : CategoryTheory.CommSq 
f g h i), s.cocone.inl = h
参数：s : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cocone_inl (s : CommSq f g h i) : s.cocone.inl = h :=
  rfl

@[simp]
/-
**CategoryTheory.CommSq.cocone_inr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {W X Y Z : 
C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z} (s : CategoryTheory.CommSq 
f g h i), s.cocone.inr = i
参数：s : CategoryTheory.CommSq f g h i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cocone_inr (s : CommSq f g h i) : s.cocone.inr = i :=
  rfl

end CommSq

end CategoryTheory

