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

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
/-
**CategoryTheory.RegularMono** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：RegularMono (f : X ⟶ Y) where /-- An object in `C` -/ Z : C /-- A map from
 the codomain of `f` to `Z` -/ left : Y ⟶ Z /-- Another map from the codomain of
 `f` to `Z` -/ right : Y ⟶ Z /-- `f` equalizes the two maps -/ w : f ≫ left = f 
≫ right
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular monomorphism is a morphism which is the equalizer of some parallel pai
r.
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

/-- Every regular monomorphism is a monomorphism. -/
/-
**CategoryTheory.RegularMono.mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Regu
larMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f :
 X ⟶ Y} (h : CategoryTheory.RegularMono f),   CategoryTheory.Mono f
参数：h : CategoryTheory.RegularMono f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.mono_of_isLimit_fork`：mono_of_isLimit_fork {c : Fo
rk f g} (i : IsLimit c) : Mono (Fork.ι c)
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…

--- 原说明 ---
Every regular monomorphism is a monomorphism.
-/
lemma RegularMono.mono {f : X ⟶ Y} (h : RegularMono f) : Mono f :=
  mono_of_isLimit_fork h.isLimit

set_option backward.isDefEq.respectTransparency.types false in
/-- Every isomorphism is a regular monomorphism. -/
/-
**CategoryTheory.RegularMono.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Reg
ularMono`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(e : X ≅ Y) → CategoryTheory.RegularMono e.hom
参数：e : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every isomorphism is a regular monomorphism.
-/
def RegularMono.ofIso (e : X ≅ Y) : RegularMono e.hom where
  Z := Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι ≫ e.inv) (by simp) fun s m w ↦ by simp [← w]

set_option backward.isDefEq.respectTransparency false in
/-- Regular monomorphisms are preserved by isomorphisms in the arrow category. -/
/-
**CategoryTheory.RegularMono.ofArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.RegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y X
' Y' : C} →       {f : X ⟶ Y} →         {g : X' ⟶ Y'} →           (CategoryTheor
y.Arrow.mk f ≅ CategoryTheory.Arrow.mk g) →             CategoryTheory.RegularMo
no f → CategoryTheory.RegularMono g
参数：CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…

--- 原说明 ---
Regular monomorphisms are preserved by isomorphisms in the arrow category.
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

/-- `IsRegularMono f` is the assertion that `f` is a regular monomorphism. -/
/-
**CategoryTheory.IsRegularMono** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsRegularMono f` is the assertion that `f` is a regular monomorphism.
-/
class IsRegularMono {X Y : C} (f : X ⟶ Y) : Prop where
  regularMono : Nonempty (RegularMono f)

variable (C) in
/-- The `MorphismProperty C` satisfied by regular monomorphisms in `C`. -/
/-
**CategoryTheory.MorphismProperty.regularMono** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.MorphismProperty`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MorphismProperty C` satisfied by regular monomorphisms in `C`.
-/
def MorphismProperty.regularMono : MorphismProperty C := fun _ _ f => IsRegularMono f

@[simp]
/-
**CategoryTheory.MorphismProperty.regularMono_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y),   CategoryTheory.MorphismProperty.regularMono C f ↔ CategoryTheory.IsRe
gularMono f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem MorphismProperty.regularMono_iff (f : X ⟶ Y) :
    (MorphismProperty.regularMono C) f ↔ IsRegularMono f :=
  Iff.rfl
/-
**CategoryTheory.MorphismProperty.regularMono.containsIdentities** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.MorphismProperty.regularMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C],   (CategoryTh
eory.MorphismProperty.regularMono C).ContainsIdentities
参数：CategoryTheory.MorphismProperty.regularMono C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MorphismProperty.regularMono.containsIdentities :
    (MorphismProperty.regularMono C).ContainsIdentities where
  id_mem _ := ⟨⟨RegularMono.ofIso <| Iso.refl _⟩⟩
/-
**CategoryTheory.MorphismProperty.regularMono.respectsIso** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.MorphismProperty.regularMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C], (CategoryTheo
ry.MorphismProperty.regularMono C).RespectsIso
参数：CategoryTheory.MorphismProperty.regularMono C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.of_respects_arrow_iso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C),   (∀ (f g : CategoryTheory.Arrow C) (x : f…
· 使用定理 `CategoryTheory.IsRegularMono.regularMono`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsR
egularMono f], Nonempty (Categ…
-/
instance MorphismProperty.regularMono.respectsIso :
    (MorphismProperty.regularMono C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h ↦ ⟨⟨.ofArrowIso e (h := h.regularMono.some)⟩⟩)
/-
**CategoryTheory.isRegularMono_of_regularMono** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory`。
形式化陈述：isRegularMono_of_regularMono {f : X ⟶ Y} (h : RegularMono f) : IsRegularMo
no f
参数：h : RegularMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRegularMono_of_regularMono {f : X ⟶ Y} (h : RegularMono f) : IsRegularMono f := ⟨⟨h⟩⟩

/-- Given `IsRegularMono f`, a choice of data for `RegularMono f`. -/
/-
**CategoryTheory.IsRegularMono.getStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.IsRegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [CategoryTheory.IsRegularMono f] → CategoryTheory.RegularMon
o f
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularMono.regularMono`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsR
egularMono f], Nonempty (Categ…

--- 原说明 ---
Given `IsRegularMono f`, a choice of data for `RegularMono f`.
-/
def IsRegularMono.getStruct (f : X ⟶ Y) [IsRegularMono f] : RegularMono f :=
  IsRegularMono.regularMono.some

/-- An equalizer diagram gives rise to a regular monomorphism. -/
/-
**CategoryTheory.Fork.IsLimit.regularMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Fork.IsLimit`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {A B :
 C} →       {p₁ p₂ : A ⟶ B} →         {c : CategoryTheory.Limits.Fork p₁ p₂} → C
ategoryTheory.Limits.IsLimit c → CategoryTheory.RegularMono c.ι
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.condition`：∀ {C : Type u} {X Y : C} [inst : C
ategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Fork f
 g),   CategoryTheory.Cate…

--- 原说明 ---
An equalizer diagram gives rise to a regular monomorphism.
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

/-- The target of the equalizer diagram for `f`. -/
/-
**CategoryTheory.IsRegularMono.Z** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsReg
ularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} 
→ (f : X ⟶ Y) → [CategoryTheory.IsRegularMono f] → C
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The target of the equalizer diagram for `f`.
-/
def IsRegularMono.Z : C := (IsRegularMono.getStruct f).Z

/-- The "left" map `Y ⟶ Z`. -/
/-
**CategoryTheory.IsRegularMono.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
RegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [inst_1 : CategoryTheory.IsRegularMono f] → Y ⟶ CategoryTheo
ry.IsRegularMono.Z f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "left" map `Y ⟶ Z`.
-/
def IsRegularMono.left : Y ⟶ Z f := (IsRegularMono.getStruct f).left

/-- The "right" map `Y ⟶ Z`. -/
/-
**CategoryTheory.IsRegularMono.right** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.I
sRegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [inst_1 : CategoryTheory.IsRegularMono f] → Y ⟶ CategoryTheo
ry.IsRegularMono.Z f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "right" map `Y ⟶ Z`.
-/
def IsRegularMono.right : Y ⟶ Z f := (IsRegularMono.getStruct f).right

/-- The equalizer condition. -/
/-
**CategoryTheory.IsRegularMono.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsReg
ularMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularMono f],   CategoryTheory.CategorySt
ruct.comp f (CategoryTheory.IsRegularMono.left f) =     CategoryTheory.CategoryS
truct.comp f (CategoryTheory.IsRegularMono.right f)
参数：f : X ⟶ Y；CategoryTheory.IsRegularMono.left f；CategoryTheory.IsRegularMono.ri
ght f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…

--- 原说明 ---
The equalizer condition.
-/
lemma IsRegularMono.w : f ≫ left f = f ≫ right f := (IsRegularMono.getStruct f).w

/-- The fork is in fact an equalizer. -/
/-
**CategoryTheory.IsRegularMono.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.IsRegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} →       (f : X ⟶ Y) →         [inst_1 : CategoryTheory.IsRegularMono f] → Ca
tegoryTheory.Limits.IsLimit (CategoryTheory.Limits.Fork.ofι f ⋯)
参数：f : X ⟶ Y；CategoryTheory.Limits.Fork.ofι f ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork is in fact an equalizer.
-/
def IsRegularMono.isLimit : IsLimit <| Fork.ofι _ (w f) := (IsRegularMono.getStruct f).isLimit

/-- Lift a morphism `k : W ⟶ Y`, equalized by the two morphisms `left` and `right`, along `f`. -/
/-
**CategoryTheory.IsRegularMono.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
RegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y W
 : C} →       (f : X ⟶ Y) →         [inst_1 : CategoryTheory.IsRegularMono f] → 
          (k : W ⟶ Y) →             CategoryTheory.CategoryStruct.comp k (Catego
ryTheory.IsRegularMono.left f) =                 CategoryTheory.CategoryStruct.c
omp k (CategoryTheory.IsRegularMono.right f) →               (W ⟶ X)
参数：f : X ⟶ Y；k : W ⟶ Y；CategoryTheory.IsRegularMono.left f；CategoryTheory.IsRegu
larMono.right f；W ⟶ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularMo
no f],   CategoryThe…

--- 原说明 ---
Lift a morphism `k : W ⟶ Y`, equalized by the two morphisms `left` and `right`, 
along `f`.
-/
def IsRegularMono.lift {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) : W ⟶ X :=
  Fork.IsLimit.lift (isLimit f) k h

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsRegularMono.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsR
egularMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y W : C} (f
 : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularMono f] (k : W ⟶ Y)   (h :     Cat
egoryTheory.CategoryStruct.comp k (CategoryTheory.IsRegularMono.left f) =       
CategoryTheory.CategoryStruct.comp k (CategoryTheory.IsRegularMono.right f)),   
CategoryTheory.CategoryStruct.comp (CategoryTheory.IsRegularMono.lift f k h) f =
 k
参数：f : X ⟶ Y；k : W ⟶ Y；h :     CategoryTheory.CategoryStruct.comp k (CategoryThe
ory.IsRegularMono.left f) =       CategoryTheory.CategoryStruct.comp k (Category
Theory.IsRegularMono.right f)；CategoryTheory.IsRegularMono.lift f k h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.lift_ι`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s t : CategoryTheory.Limits
.Fork f g}   (hs : CategoryTheo…
· 使用定理 `CategoryTheory.IsRegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularMo
no f],   CategoryThe…
-/
lemma IsRegularMono.fac {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) : lift f k h ≫ f = k :=
  Fork.IsLimit.lift_ι (isLimit f)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsRegularMono.uniq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
RegularMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y W : C} (f
 : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularMono f] (k : W ⟶ Y)   (h :     Cat
egoryTheory.CategoryStruct.comp k (CategoryTheory.IsRegularMono.left f) =       
CategoryTheory.CategoryStruct.comp k (CategoryTheory.IsRegularMono.right f))   (
m : W ⟶ X), CategoryTheory.CategoryStruct.comp m f = k → m = CategoryTheory.IsRe
gularMono.lift f k h
参数：f : X ⟶ Y；k : W ⟶ Y；h :     CategoryTheory.CategoryStruct.comp k (CategoryThe
ory.IsRegularMono.left f) =       CategoryTheory.CategoryStruct.comp k (Category
Theory.IsRegularMono.right f)；m : W ⟶ X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `CategoryTheory.IsRegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularMo
no f],   CategoryThe…
· 使用定理 `CategoryTheory.Limits.Fork.IsLimit.existsUnique`：∀ {C : Type u} {X Y : C
} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Li
mits.Fork f g}   (hs : CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsRegularMono.fac`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y W : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegul
arMono f] (k : W ⟶ Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsRegularMono.uniq {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) (m : W ⟶ X) (hm : m ≫ f = k) : m = lift f k h :=
  Fork.IsLimit.existsUnique (isLimit f) k h |>.unique hm <| by simp

end IsRegularMono

set_option backward.isDefEq.respectTransparency false in
/-- The chosen equalizer of a parallel pair is a regular monomorphism. -/
/-
**CategoryTheory.RegularMono.equalizer** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.RegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} →       (g h : X ⟶ Y) →         [inst_1 : CategoryTheory.Limits.HasLimit (Ca
tegoryTheory.Limits.parallelPair g h)] →           CategoryTheory.RegularMono (C
ategoryTheory.Limits.equalizer.ι g h)
参数：g h : X ⟶ Y；CategoryTheory.Limits.parallelPair g h；CategoryTheory.Limits.equa
lizer.ι g h。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…

--- 原说明 ---
The chosen equalizer of a parallel pair is a regular monomorphism.
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    IsRegularMono (equalizer.ι g h) :=
  isRegularMono_of_regularMono <| RegularMono.equalizer g h

/-- Every split monomorphism is a regular monomorphism. -/
/-
**CategoryTheory.RegularMono.ofIsSplitMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.RegularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [CategoryTheory.IsSplitMono f] → CategoryTheory.RegularMono 
f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every split monomorphism is a regular monomorphism.
-/
def RegularMono.ofIsSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    RegularMono f where
  Z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (f : X ⟶ Y) [IsSplitMono f] :
    IsRegularMono f :=
  isRegularMono_of_regularMono <| .ofIsSplitMono f

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `RegularMono.left` and
`RegularMono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
/-
**CategoryTheory.RegularMono.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Reg
ularMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y W
 : C} →       {f : X ⟶ Y} →         (hf : CategoryTheory.RegularMono f) →       
    (k : W ⟶ Y) →             CategoryTheory.CategoryStruct.comp k hf.left = Cat
egoryTheory.CategoryStruct.comp k hf.right →               { l // CategoryTheory
.CategoryStruct.comp l f = k }
参数：hf : CategoryTheory.RegularMono f；k : W ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…

--- 原说明 ---
If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `RegularMono.left`
 and
`RegularMono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`.
-/
def RegularMono.lift' {W : C} {f : X ⟶ Y} (hf : RegularMono f) (k : W ⟶ Y)
    (h : k ≫ hf.left = k ≫ hf.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' hf.isLimit _ h

/-- The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `Pullback.sndOfMono` for the basic monomorphism version, and
`regularOfIsPullbackFstOfRegular` for the flipped version.
-/
/-
**CategoryTheory.regularOfIsPullbackSndOfRegular** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h :
 Q ⟶ S} {k : R ⟶ S} (hr : RegularMono h) (comm : f ≫ h = g ≫ k) (t : IsLimit (Pu
llbackCone.mk _ _ comm)) : RegularMono g where Z
参数：hr : RegularMono h；comm : f ≫ h = g ≫ k；t : IsLimit (PullbackCone.mk _ _ comm
)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…

--- 原说明 ---
The second leg of a pullback cone is a regular monomorphism if the right compone
nt is too.

See also `Pullback.sndOfMono` for the basic monomorphism version, and
`regularOfIsPullbackFstOfRegular` for the flipped version.
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
      rw [Category.assoc, s.condition, Category.assoc]
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

/-- The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `Pullback.fstOfMono` for the basic monomorphism version, and
`regularOfIsPullbackSndOfRegular` for the flipped version.
-/
/-
**CategoryTheory.regularOfIsPullbackFstOfRegular** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h :
 Q ⟶ S} {k : R ⟶ S} (hk : RegularMono k) (comm : f ≫ h = g ≫ k) (t : IsLimit (Pu
llbackCone.mk _ _ comm)) : RegularMono f
参数：hk : RegularMono k；comm : f ≫ h = g ≫ k；t : IsLimit (PullbackCone.mk _ _ comm
)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first leg of a pullback cone is a regular monomorphism if the left component
 is too.

See also `Pullback.fstOfMono` for the basic monomorphism version, and
`regularOfIsPullbackSndOfRegular` for the flipped version.
-/
def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hk : RegularMono k) (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono f :=
  regularOfIsPullbackSndOfRegular hk comm.symm (PullbackCone.flipIsLimit t)

/-- Any regular monomorphism is a strong monomorphism. -/
/-
**CategoryTheory.RegularMono.strongMono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.RegularMono`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f :
 X ⟶ Y} (h : CategoryTheory.RegularMono f),   CategoryTheory.StrongMono f
参数：h : CategoryTheory.RegularMono f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (h : CategoryTheory.RegularMono f),  
 CategoryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mk'`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {P Q : C} {f : Q ⟶ P} [CategoryTheory.Mono f],   (∀ (Y X : C) (z
 : Y ⟶ X),       Ca…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eq_whisker`：eq_whisker {f g : X ⟶ Y} (w : f = g) (h : Y ⟶
 Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.HasLift.mk'`：mk' (l : sq.LiftStruct) : HasLift sq
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…

--- 原说明 ---
Any regular monomorphism is a strong monomorphism.
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (f : X ⟶ Y) [IsRegularMono f] : StrongMono f :=
  IsRegularMono.getStruct f |>.strongMono

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
/-
**CategoryTheory.isIso_of_regularMono_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：isIso_of_regularMono_of_epi (f : X ⟶ Y) (h : RegularMono f) [Epi f] : IsIs
o f
参数：f : X ⟶ Y；h : RegularMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.strongMono`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (h : CategoryTheory.RegularMono
 f),   CategoryTheory.Stron…
· 使用定理 `CategoryTheory.isIso_of_epi_of_strongMono`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.Epi f]   [Cate
goryTheory.StrongMono f], Categ…

--- 原说明 ---
A regular monomorphism is an isomorphism if it is an epimorphism.
-/
theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) (h : RegularMono f) [Epi f] : IsIso f :=
  have := RegularMono.strongMono h
  isIso_of_epi_of_strongMono _

section

variable (C)

/-- A regular mono category is a category in which every monomorphism is regular. -/
/-
**CategoryTheory.IsRegularMonoCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular mono category is a category in which every monomorphism is regular.
-/
class IsRegularMonoCategory : Prop where
  /-- Every monomorphism is a regular monomorphism -/
  regularMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsRegularMono f

end

/-- In a category in which every monomorphism is regular, we can express every monomorphism as
an equalizer. This is not an instance because it would create an instance loop. -/
/-
**CategoryTheory.regularMonoOfMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：regularMonoOfMono [IsRegularMonoCategory C] (f : X ⟶ Y) [Mono f] : Regular
Mono f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularMonoCategory.regularMonoOfMono`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.IsRegularMono
Category C] {X Y : C}   (f : X ⟶ Y) [Categor…

--- 原说明 ---
In a category in which every monomorphism is regular, we can express every monom
orphism as
an equalizer. This is not an instance because it would create an instance loop.
-/
def regularMonoOfMono [IsRegularMonoCategory C] (f : X ⟶ Y) [Mono f] : RegularMono f :=
  have := IsRegularMonoCategory.regularMonoOfMono f
  IsRegularMono.getStruct f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    IsRegularMonoCategory C where
  regularMonoOfMono f _ :=
    haveI := isSplitMono_of_mono f
    isRegularMono_of_regularMono <| RegularMono.ofIsSplitMono f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) strongMonoCategory_of_regularMonoCategory [IsRegularMonoCategory C] :
    StrongMonoCategory C where
  strongMono_of_mono f _ :=
    RegularMono.strongMono <| regularMonoOfMono f

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
/-
**CategoryTheory.RegularEpi** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：RegularEpi (f : X ⟶ Y) where /-- An object from `C` -/ W : C /-- Two maps 
to the domain of `f` -/ (left right : W ⟶ X) /-- `f` coequalizes the two maps -/
 w : left ≫ f = right ≫ f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular epimorphism is a morphism which is the coequalizer of some parallel pa
ir.
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

/-- Every regular epimorphism is an epimorphism. -/
/-
**CategoryTheory.RegularEpi.epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Regula
rEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y) (h : CategoryTheory.RegularEpi f),   CategoryTheory.Epi f
参数：f : X ⟶ Y；h : CategoryTheory.RegularEpi f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.epi_of_isColimit_cofork`：epi_of_isColimit_cofork {
c : Cofork f g} (i : IsColimit c) : Epi c.π
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
Every regular epimorphism is an epimorphism.
-/
lemma RegularEpi.epi (f : X ⟶ Y) (h : RegularEpi f) : Epi f :=
  epi_of_isColimit_cofork h.isColimit

set_option backward.isDefEq.respectTransparency.types false in
/-- Every isomorphism is a regular epimorphism. -/
/-
**CategoryTheory.RegularEpi.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Regu
larEpi`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(e : X ≅ Y) → CategoryTheory.RegularEpi e.hom
参数：e : X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every isomorphism is a regular epimorphism.
-/
def RegularEpi.ofIso (e : X ≅ Y) : RegularEpi e.hom where
  W := X
  left := 𝟙 X
  right := 𝟙 X
  isColimit := Cofork.IsColimit.mk _ (fun s ↦ e.inv ≫ s.π) (by simp) fun s m w ↦ by
    simp [← w]

set_option backward.isDefEq.respectTransparency false in
/-- Regular epimorphisms are preserved by isomorphisms in the arrow category. -/
/-
**CategoryTheory.RegularEpi.ofArrowIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.RegularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y X
' Y' : C} →       {f : X ⟶ Y} →         {g : X' ⟶ Y'} →           (CategoryTheor
y.Arrow.mk f ≅ CategoryTheory.Arrow.mk g) →             CategoryTheory.RegularEp
i f → CategoryTheory.RegularEpi g
参数：CategoryTheory.Arrow.mk f ≅ CategoryTheory.Arrow.mk g。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
Regular epimorphisms are preserved by isomorphisms in the arrow category.
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

/-- `IsRegularEpi f` is the assertion that `f` is a regular epimorphism. -/
/-
**CategoryTheory.IsRegularEpi** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsRegularEpi f` is the assertion that `f` is a regular epimorphism.
-/
class IsRegularEpi {X Y : C} (f : X ⟶ Y) : Prop where
  regularEpi : Nonempty (RegularEpi f)

variable (C) in
/-- The `MorphismProperty C` satisfied by regular epimorphisms in `C`. -/
/-
**CategoryTheory.MorphismProperty.regularEpi** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.MorphismProperty`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → CategoryTheo
ry.MorphismProperty C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MorphismProperty C` satisfied by regular epimorphisms in `C`.
-/
def MorphismProperty.regularEpi : MorphismProperty C := fun _ _ f => IsRegularEpi f

@[simp]
/-
**CategoryTheory.MorphismProperty.regularEpi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y),   CategoryTheory.MorphismProperty.regularEpi C f ↔ CategoryTheory.IsReg
ularEpi f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem MorphismProperty.regularEpi_iff (f : X ⟶ Y) :
    (MorphismProperty.regularEpi C) f ↔ IsRegularEpi f :=
  Iff.rfl
/-
**CategoryTheory.MorphismProperty.regularEpi.containsIdentities** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.MorphismProperty.regularEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C],   (CategoryTh
eory.MorphismProperty.regularEpi C).ContainsIdentities
参数：CategoryTheory.MorphismProperty.regularEpi C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MorphismProperty.regularEpi.containsIdentities :
    (MorphismProperty.regularEpi C).ContainsIdentities where
  id_mem _ := ⟨⟨RegularEpi.ofIso <| Iso.refl _⟩⟩
/-
**CategoryTheory.MorphismProperty.regularEpi.respectsIso** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MorphismProperty.regularEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C], (CategoryTheo
ry.MorphismProperty.regularEpi C).RespectsIso
参数：CategoryTheory.MorphismProperty.regularEpi C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.of_respects_arrow_iso`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Morphism
Property C),   (∀ (f g : CategoryTheory.Arrow C) (x : f…
· 使用定理 `CategoryTheory.IsRegularEpi.regularEpi`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsReg
ularEpi f], Nonempty (Catego…
-/
instance MorphismProperty.regularEpi.respectsIso :
    (MorphismProperty.regularEpi C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h ↦ ⟨⟨.ofArrowIso e (h := h.regularEpi.some)⟩⟩)
/-
**CategoryTheory.isRegularEpi_of_regularEpi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isRegularEpi_of_regularEpi {f : X ⟶ Y} (h : RegularEpi f) : IsRegularEpi f
参数：h : RegularEpi f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isRegularEpi_of_regularEpi {f : X ⟶ Y} (h : RegularEpi f) : IsRegularEpi f := ⟨⟨h⟩⟩

/-- Given `IsRegularEpi f`, a choice of data for `RegularEpi f`. -/
/-
**CategoryTheory.IsRegularEpi.getStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsRegularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [h : CategoryTheory.IsRegularEpi f] → CategoryTheory.Regular
Epi f
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularEpi.regularEpi`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsReg
ularEpi f], Nonempty (Catego…

--- 原说明 ---
Given `IsRegularEpi f`, a choice of data for `RegularEpi f`.
-/
def IsRegularEpi.getStruct (f : X ⟶ Y) [h : IsRegularEpi f] : RegularEpi f :=
  h.regularEpi.some

/-- A coequalizer diagram gives rise to a regular epimorphism. -/
/-
**CategoryTheory.Cofork.IsColimit.regularEpi** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Cofork.IsColimit`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {A B :
 C} →       {p₁ p₂ : A ⟶ B} →         {c : CategoryTheory.Limits.Cofork p₁ p₂} →
 CategoryTheory.Limits.IsColimit c → CategoryTheory.RegularEpi c.π
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…

--- 原说明 ---
A coequalizer diagram gives rise to a regular epimorphism.
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

/-- The source of the coequalizer diagram for `f`. -/
/-
**CategoryTheory.IsRegularEpi.W** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsRegu
larEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} 
→ (f : X ⟶ Y) → [CategoryTheory.IsRegularEpi f] → C
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The source of the coequalizer diagram for `f`.
-/
def IsRegularEpi.W : C := (IsRegularEpi.getStruct f).W

/-- The "left" map `W ⟶ X`. -/
/-
**CategoryTheory.IsRegularEpi.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsR
egularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [inst_1 : CategoryTheory.IsRegularEpi f] → CategoryTheory.Is
RegularEpi.W f ⟶ X
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "left" map `W ⟶ X`.
-/
def IsRegularEpi.left : W f ⟶ X := (IsRegularEpi.getStruct f).left

/-- The "right" map `W ⟶ X`. -/
/-
**CategoryTheory.IsRegularEpi.right** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Is
RegularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [inst_1 : CategoryTheory.IsRegularEpi f] → CategoryTheory.Is
RegularEpi.W f ⟶ X
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "right" map `W ⟶ X`.
-/
def IsRegularEpi.right : W f ⟶ X := (IsRegularEpi.getStruct f).right

/-- The coequalizer condition. -/
/-
**CategoryTheory.IsRegularEpi.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsRegu
larEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi f],   CategoryTheory.CategoryStr
uct.comp (CategoryTheory.IsRegularEpi.left f) f =     CategoryTheory.CategoryStr
uct.comp (CategoryTheory.IsRegularEpi.right f) f
参数：f : X ⟶ Y；CategoryTheory.IsRegularEpi.left f；CategoryTheory.IsRegularEpi.righ
t f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
The coequalizer condition.
-/
lemma IsRegularEpi.w : left f ≫ f = right f ≫ f := (IsRegularEpi.getStruct f).w

/-- The cofork is in fact a coequalizer. -/
/-
**CategoryTheory.IsRegularEpi.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.IsRegularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} →       (f : X ⟶ Y) →         [inst_1 : CategoryTheory.IsRegularEpi f] →    
       CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofork.ofπ f ⋯)
参数：f : X ⟶ Y；CategoryTheory.Limits.Cofork.ofπ f ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork is in fact a coequalizer.
-/
def IsRegularEpi.isColimit : IsColimit <| Cofork.ofπ _ (w f) := (IsRegularEpi.getStruct f).isColimit

/--
Descend a morphism `k : X ⟶ Z`, coequalized by the two morphisms `left` and `right`, along `f`.
-/
/-
**CategoryTheory.IsRegularEpi.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.IsR
egularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       (f : X ⟶ Y) →         [inst_1 : CategoryTheory.IsRegularEpi f] →  
         (k : X ⟶ Z) →             CategoryTheory.CategoryStruct.comp (CategoryT
heory.IsRegularEpi.left f) k =                 CategoryTheory.CategoryStruct.com
p (CategoryTheory.IsRegularEpi.right f) k →               (Y ⟶ Z)
参数：f : X ⟶ Y；k : X ⟶ Z；CategoryTheory.IsRegularEpi.left f；CategoryTheory.IsRegul
arEpi.right f；Y ⟶ Z。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi
 f],   CategoryTheo…

--- 原说明 ---
Descend a morphism `k : X ⟶ Z`, coequalized by the two morphisms `left` and `rig
ht`, along `f`.
-/
def IsRegularEpi.desc {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
    (h : left f ≫ k = right f ≫ k) : Y ⟶ Z :=
  Cofork.IsColimit.desc (isColimit f) k h

@[reassoc (attr := simp)]
/-
**CategoryTheory.IsRegularEpi.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsRe
gularEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f
 : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi f] (k : X ⟶ Z)   (h :     Cate
goryTheory.CategoryStruct.comp (CategoryTheory.IsRegularEpi.left f) k =       Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.IsRegularEpi.right f) k),   Cat
egoryTheory.CategoryStruct.comp f (CategoryTheory.IsRegularEpi.desc f k h) = k
参数：f : X ⟶ Y；k : X ⟶ Z；h :     CategoryTheory.CategoryStruct.comp (CategoryTheor
y.IsRegularEpi.left f) k =       CategoryTheory.CategoryStruct.comp (CategoryThe
ory.IsRegularEpi.right f) k；CategoryTheory.IsRegularEpi.desc f k h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc`：∀ {C : Type u} {X Y : C} 
[inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryTheory.
Limits.Cofork f g} (hs : CategoryTh…
· 使用定理 `CategoryTheory.IsRegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi
 f],   CategoryTheo…
-/
lemma IsRegularEpi.fac {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
    (h : left f ≫ k = right f ≫ k) : f ≫ desc f k h = k :=
  Cofork.IsColimit.π_desc (isColimit f)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.IsRegularEpi.uniq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsR
egularEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f
 : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi f] (k : X ⟶ Z)   (h :     Cate
goryTheory.CategoryStruct.comp (CategoryTheory.IsRegularEpi.left f) k =       Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.IsRegularEpi.right f) k)   (m :
 Y ⟶ Z), CategoryTheory.CategoryStruct.comp f m = k → m = CategoryTheory.IsRegul
arEpi.desc f k h
参数：f : X ⟶ Y；k : X ⟶ Z；h :     CategoryTheory.CategoryStruct.comp (CategoryTheor
y.IsRegularEpi.left f) k =       CategoryTheory.CategoryStruct.comp (CategoryThe
ory.IsRegularEpi.right f) k；m : Y ⟶ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `CategoryTheory.IsRegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegularEpi
 f],   CategoryTheo…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.existsUnique`：∀ {C : Type u} {X Y
 : C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheor
y.Limits.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsRegularEpi.fac`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.IsRegula
rEpi f] (k : X ⟶ Z)  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsRegularEpi.uniq {Z : C} (f : X ⟶ Y) [IsRegularEpi f] (k : X ⟶ Z)
    (h : left f ≫ k = right f ≫ k) (m : Y ⟶ Z) (hm : f ≫ m = k) : m = desc f k h :=
  Cofork.IsColimit.existsUnique (isColimit f) k h |>.unique hm <| by simp

end IsRegularEpi

set_option backward.isDefEq.respectTransparency false in
/-- The chosen coequalizer of a parallel pair is a regular epimorphism. -/
/-
**CategoryTheory.coequalizerRegular** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] : Regular
Epi (coequalizer.π g h) where W
参数：g h : X ⟶ Y；parallelPair g h。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…

--- 原说明 ---
The chosen coequalizer of a parallel pair is a regular epimorphism.
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
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
    IsRegularEpi (coequalizer.π g h) :=
  ⟨⟨coequalizerRegular g h⟩⟩

/-- A morphism which is a coequalizer for its kernel pair is a regular epi. -/
/-
**CategoryTheory.regularEpiOfKernelPair** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：regularEpiOfKernelPair {B X : C} (f : X ⟶ B) [HasPullback f f] (hc : IsCol
imit (Cofork.ofπ f pullback.condition)) : RegularEpi f where W
参数：f : X ⟶ B；hc : IsColimit (Cofork.ofπ f pullback.condition)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
A morphism which is a coequalizer for its kernel pair is a regular epi.
-/
def regularEpiOfKernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := hc

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.IsRegularEpi.of_epi_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.IsRegularEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X B : C} {f :
 X ⟶ B}   [inst_1 : CategoryTheory.Limits.HasPullback f f] [CategoryTheory.Epi f
],   (∀ ⦃Z : C⦄ ⦃g : X ⟶ Z⦄,       CategoryTheory.CategoryStruct.comp (CategoryT
heory.Limits.pullback.fst f f) g =           CategoryTheory.CategoryStruct.comp 
(CategoryTheory.Limits.pullback.snd f f) g →         ∃ u, CategoryTheory.Categor
yStruct.comp f u = g) →     CategoryTheory.IsRegularEpi f
参数：∀ ⦃Z : C⦄ ⦃g : X ⟶ Z⦄,       CategoryTheory.CategoryStruct.comp (CategoryTheo
ry.Limits.pullback.fst f f) g =           CategoryTheory.CategoryStruct.comp (Ca
tegoryTheory.Limits.pullback.snd f f) g →         ∃ u, CategoryTheory.CategorySt
ruct.comp f u = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.Cofork.condition`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} (t : CategoryTheory.Limits.Cofo
rk f g),   CategoryTheory.Ca…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma IsRegularEpi.of_epi_of_exists {X B : C} {f : X ⟶ B} [HasPullback f f] [Epi f]
    (h : ∀ ⦃Z : C⦄ ⦃g : X ⟶ Z⦄, pullback.fst f f ≫ g = pullback.snd f f ≫ g →
      ∃ (u : B ⟶ Z), f ≫ u = g) :
    IsRegularEpi f := by
  refine ⟨⟨regularEpiOfKernelPair _ <| Cofork.IsColimit.mk' _ fun s ↦ ?_⟩⟩
  choose g hg using h s.condition
  refine ⟨g, hg, fun hm ↦ ?_⟩
  rwa [← cancel_epi f, hg]

/-- The data of an `EffectiveEpi` structure on a `RegularEpi`. -/
/-
**CategoryTheory.effectiveEpiStructOfRegularEpi** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：effectiveEpiStructOfRegularEpi {B X : C} {f : X ⟶ B} (hf : RegularEpi f) :
 EffectiveEpiStruct f where desc _ h
参数：hf : RegularEpi f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
The data of an `EffectiveEpi` structure on a `RegularEpi`.
-/
def effectiveEpiStructOfRegularEpi {B X : C} {f : X ⟶ B} (hf : RegularEpi f) :
    EffectiveEpiStruct f where
  desc _ h := Cofork.IsColimit.desc hf.isColimit _ (h _ _ hf.w)
  fac _ _ := Cofork.IsColimit.π_desc' hf.isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext hf.isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)
/-
**CategoryTheory.RegularEpi.effectiveEpi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.RegularEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {B X : C} {f :
 X ⟶ B} (h : CategoryTheory.RegularEpi f),   CategoryTheory.EffectiveEpi f
参数：h : CategoryTheory.RegularEpi f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RegularEpi.effectiveEpi {B X : C} {f : X ⟶ B} (h : RegularEpi f) : EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfRegularEpi h⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {B X : C} {f : X ⟶ B} [h : IsRegularEpi f] : EffectiveEpi f :=
  IsRegularEpi.getStruct f |>.effectiveEpi

/-- A morphism which is a coequalizer for its kernel pair is an effective epi. -/
/-
**CategoryTheory.effectiveEpi_of_kernelPair** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory`。
形式化陈述：effectiveEpi_of_kernelPair {B X : C} (f : X ⟶ B) [HasPullback f f] (hc : I
sColimit (Cofork.ofπ f pullback.condition)) : EffectiveEpi f
参数：f : X ⟶ B；hc : IsColimit (Cofork.ofπ f pullback.condition)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.RegularEpi.effectiveEpi`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} (h : CategoryTheory.RegularEpi
 f),   CategoryTheory.Effect…

--- 原说明 ---
A morphism which is a coequalizer for its kernel pair is an effective epi.
-/
theorem effectiveEpi_of_kernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : EffectiveEpi f :=
  RegularEpi.effectiveEpi <| regularEpiOfKernelPair f hc

set_option backward.isDefEq.respectTransparency false in
/--
Given a kernel pair of an effective epimorphism `f : X ⟶ B`, the induced cofork is a coequalizer.
-/
/-
**CategoryTheory.isColimitCoforkOfEffectiveEpi** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：isColimitCoforkOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f] (c : 
PullbackCone f f) (hc : IsLimit c) : IsColimit (Cofork.ofπ f c.condition) where 
desc s
参数：f : X ⟶ B；c : PullbackCone f f；hc : IsLimit c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g

--- 原说明 ---
Given a kernel pair of an effective epimorphism `f : X ⟶ B`, the induced cofork 
is a coequalizer.
-/
def isColimitCoforkOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f]
    (c : PullbackCone f f) (hc : IsLimit c) :
    IsColimit (Cofork.ofπ f c.condition) where
  desc s := EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg, Category.assoc,
        ← Cofork.app_zero_eq_comp_π_right]
      simp)
  fac s := by
    have := EffectiveEpi.fac f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg,
        Category.assoc, ← Cofork.app_zero_eq_comp_π_right]
      simp)
    rintro (_ | _)
    all_goals simp_all
  uniq _ _ h := EffectiveEpi.uniq f _ _ _ (h WalkingParallelPair.one)

/-- An effective epi which has a kernel pair is a regular epi. -/
/-
**CategoryTheory.regularEpiOfEffectiveEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：regularEpiOfEffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f] [Effectiv
eEpi f] : RegularEpi f where W
参数：f : X ⟶ B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
An effective epi which has a kernel pair is a regular epi.
-/
def regularEpiOfEffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit _ _)
/-
**CategoryTheory.isRegularEpi_of_EffectiveEpi** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory`。
形式化陈述：isRegularEpi_of_EffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f] [Effe
ctiveEpi f] : IsRegularEpi f
参数：f : X ⟶ B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isRegularEpi_of_regularEpi`：isRegularEpi_of_regularEpi {f
 : X ⟶ Y} (h : RegularEpi f) : IsRegularEpi f
-/
instance isRegularEpi_of_EffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : IsRegularEpi f :=
  isRegularEpi_of_regularEpi <| regularEpiOfEffectiveEpi f
/-
**CategoryTheory.isRegularEpi_iff_effectiveEpi** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：isRegularEpi_iff_effectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f] : Is
RegularEpi f ↔ EffectiveEpi f
参数：f : X ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…
-/
lemma isRegularEpi_iff_effectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f] :
    IsRegularEpi f ↔ EffectiveEpi f :=
  ⟨fun ⟨_⟩ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- Let `p : Y ⟶ X` be an effective epimorphism, `p₁ : Z ⟶ Y` and `p₂ : Z ⟶ Y` two
morphisms which make `Z` the pullback of two copies of `Y` over `X`.
Then, `Y ⟶ X` is the coequalizer of `p₁` and `p₂`. -/
/-
**CategoryTheory.EffectiveEpiStruct.isColimitCoforkOfIsPullback** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.EffectiveEpiStruct`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       {p : Y ⟶ X} →         CategoryTheory.EffectiveEpiStruct p →       
    {p₁ p₂ : Z ⟶ Y} →             (sq : CategoryTheory.IsPullback p₁ p₂ p p) →  
             CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofork.ofπ p
 ⋯)
参数：sq : CategoryTheory.IsPullback p₁ p₂ p p；CategoryTheory.Limits.Cofork.ofπ p ⋯
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `p : Y ⟶ X` be an effective epimorphism, `p₁ : Z ⟶ Y` and `p₂ : Z ⟶ Y` two
morphisms which make `Z` the pullback of two copies of `Y` over `X`.
Then, `Y ⟶ X` is the coequalizer of `p₁` and `p₂`.
-/
noncomputable def EffectiveEpiStruct.isColimitCoforkOfIsPullback
    {X Y Z : C} {p : Y ⟶ X} (hp : EffectiveEpiStruct p) {p₁ p₂ : Z ⟶ Y}
    (sq : IsPullback p₁ p₂ p p) :
    IsColimit (Cofork.ofπ p sq.w) :=
  Cofork.IsColimit.mk _ (fun s ↦ hp.desc s.π (fun {T} g₁ g₂ h ↦ by
      obtain ⟨l, rfl, rfl⟩ := sq.exists_lift g₁ g₂ h
      simp [s.condition]))
    (fun s ↦ hp.fac _ _)
    (fun s m hm ↦ hp.uniq _ _ _ hm)

/-- Every split epimorphism is a regular epimorphism. -/
/-
**CategoryTheory.RegularEpi.ofSplitEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.RegularEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → (f : X ⟶ Y) → [CategoryTheory.IsSplitEpi f] → CategoryTheory.RegularEpi f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every split epimorphism is a regular epimorphism.
-/
def RegularEpi.ofSplitEpi (f : X ⟶ Y) [IsSplitEpi f] : RegularEpi f where
  W := X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (f : X ⟶ Y) [IsSplitEpi f] : IsRegularEpi f :=
  isRegularEpi_of_regularEpi <| RegularEpi.ofSplitEpi f

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `RegularEpi.left` and
`RegularEpi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
/-
**CategoryTheory.RegularEpi.desc'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Regu
larEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y W
 : C} →       {f : X ⟶ Y} →         (hf : CategoryTheory.RegularEpi f) →        
   (k : X ⟶ W) →             CategoryTheory.CategoryStruct.comp hf.left k = Cate
goryTheory.CategoryStruct.comp hf.right k →               { l // CategoryTheory.
CategoryStruct.comp f l = k }
参数：hf : CategoryTheory.RegularEpi f；k : X ⟶ W。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `RegularEp
i.left` and
`RegularEpi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`.
-/
def RegularEpi.desc' {W : C} {f : X ⟶ Y} (hf : RegularEpi f) (k : X ⟶ W)
    (h : hf.left ≫ k = hf.right ≫ k) :
    { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' hf.isColimit _ h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `Pushout.sndOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutFstOfRegular` for the flipped version.
-/
/-
**CategoryTheory.regularOfIsPushoutSndOfRegular** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : 
Q ⟶ S} {k : R ⟶ S} (gr : RegularEpi g) (comm : f ≫ h = g ≫ k) (t : IsColimit (Pu
shoutCocone.mk _ _ comm)) : RegularEpi h where W
参数：gr : RegularEpi g；comm : f ≫ h = g ≫ k；t : IsColimit (PushoutCocone.mk _ _ co
mm)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
The second leg of a pushout cocone is a regular epimorphism if the right compone
nt is too.

See also `Pushout.sndOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutFstOfRegular` for the flipped version.
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
      rw [← Category.assoc, ← Category.assoc, s.condition]
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

/-- The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `Pushout.fstOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutSndOfRegular` for the flipped version.
-/
/-
**CategoryTheory.regularOfIsPushoutFstOfRegular** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : 
Q ⟶ S} {k : R ⟶ S} (hf : RegularEpi f) (comm : f ≫ h = g ≫ k) (t : IsColimit (Pu
shoutCocone.mk _ _ comm)) : RegularEpi k
参数：hf : RegularEpi f；comm : f ≫ h = g ≫ k；t : IsColimit (PushoutCocone.mk _ _ co
mm)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first leg of a pushout cocone is a regular epimorphism if the left component
 is too.

See also `Pushout.fstOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutSndOfRegular` for the flipped version.
-/
def regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hf : RegularEpi f) (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi k :=
  regularOfIsPushoutSndOfRegular hf comm.symm (PushoutCocone.flipIsColimit t)

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
/-
**CategoryTheory.isIso_of_regularEpi_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：isIso_of_regularEpi_of_mono (f : X ⟶ Y) (h : RegularEpi f) [Mono f] : IsIs
o f
参数：f : X ⟶ Y；h : RegularEpi f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isRegularEpi_of_regularEpi`：isRegularEpi_of_regularEpi {f
 : X ⟶ Y} (h : RegularEpi f) : IsRegularEpi f
· 使用定理 `CategoryTheory.isIso_of_mono_of_strongEpi`：isIso_of_mono_of_strongEpi (f
 : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f
· 使用定理 `CategoryTheory.strongEpi_of_effectiveEpi`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.Effective
Epi f],   CategoryTheory.Stron…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsRegularEpi`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {B X : C} {f : X ⟶ B} [h : CategoryTheory.IsR
egularEpi f],   CategoryTheory.Effe…

--- 原说明 ---
A regular epimorphism is an isomorphism if it is a monomorphism.
-/
theorem isIso_of_regularEpi_of_mono (f : X ⟶ Y) (h : RegularEpi f) [Mono f] : IsIso f :=
  have := isRegularEpi_of_regularEpi h
  isIso_of_mono_of_strongEpi _

section

/-- A regular monomorphism in `C` induces a regular epimorphism in `Cᵒᵖ`. -/
/-
**CategoryTheory.RegularMono.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Regula
rMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → {f : X ⟶ Y} → CategoryTheory.RegularMono f → CategoryTheory.RegularEpi f.o
p
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularMono.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularMono f),  
 CategoryTheory.Ca…

--- 原说明 ---
A regular monomorphism in `C` induces a regular epimorphism in `Cᵒᵖ`.
-/
noncomputable def RegularMono.op {X Y : C} {f : X ⟶ Y} (hf : RegularMono f) :
    RegularEpi f.op where
  W := .op hf.Z
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitOp _ _ hf.w _ rfl hf.isLimit

/-- A regular monomorphism in `Cᵒᵖ` induces a regular epimorphism in `C`. -/
/-
**CategoryTheory.RegularMono.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Regu
larMono`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 Cᵒᵖ} → {f : X ⟶ Y} → CategoryTheory.RegularMono f → CategoryTheory.RegularEpi f
.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular monomorphism in `Cᵒᵖ` induces a regular epimorphism in `C`.
-/
noncomputable def RegularMono.unop {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : RegularMono f) :
    RegularEpi f.unop where
  W := hf.Z.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isColimit := Fork.isLimitOfιEquivIsColimitUnop _ _ hf.w _ rfl hf.isLimit

/-- A regular epimorphism in `C` induces a regular monomorphism in `Cᵒᵖ`. -/
/-
**CategoryTheory.RegularEpi.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Regular
Epi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → {f : X ⟶ Y} → CategoryTheory.RegularEpi f → CategoryTheory.RegularMono f.o
p
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.RegularEpi.w`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.RegularEpi f),   C
ategoryTheory.Cat…

--- 原说明 ---
A regular epimorphism in `C` induces a regular monomorphism in `Cᵒᵖ`.
-/
noncomputable def RegularEpi.op {X Y : C} {f : X ⟶ Y} (hf : RegularEpi f) :
    RegularMono f.op where
  Z := .op hf.W
  left := hf.left.op
  right := hf.right.op
  w := by simp [← op_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitOp _ _ hf.w _ rfl hf.isColimit

/-- A regular epimorphism in `Cᵒᵖ` induces a regular monomorphism in `C`. -/
/-
**CategoryTheory.RegularEpi.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Regul
arEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 Cᵒᵖ} → {f : X ⟶ Y} → CategoryTheory.RegularEpi f → CategoryTheory.RegularMono f
.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular epimorphism in `Cᵒᵖ` induces a regular monomorphism in `C`.
-/
noncomputable def RegularEpi.unop {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : RegularEpi f) :
    RegularMono f.unop where
  Z := hf.W.unop
  left := hf.left.unop
  right := hf.right.unop
  w := by simp [← unop_comp, hf.w]
  isLimit := Cofork.isColimitOfπEquivIsLimitUnop _ _ hf.w _ rfl hf.isColimit

@[simp]
/-
**CategoryTheory.isRegularMono_op_iff_isRegularEpi** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isRegularMono_op_iff_isRegularEpi {X Y : C} (f : X ⟶ Y) : IsRegularMono f.
op ↔ IsRegularEpi f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularMono.regularMono`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsR
egularMono f], Nonempty (Categ…
· 使用定理 `CategoryTheory.IsRegularEpi.regularEpi`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsReg
ularEpi f], Nonempty (Catego…
-/
lemma isRegularMono_op_iff_isRegularEpi {X Y : C} (f : X ⟶ Y) :
    IsRegularMono f.op ↔ IsRegularEpi f :=
  ⟨fun hf ↦ ⟨⟨hf.regularMono.some.unop⟩⟩, fun hf ↦ ⟨⟨hf.regularEpi.some.op⟩⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [IsRegularEpi f] : IsRegularMono f.op := by
  simpa

@[simp]
/-
**CategoryTheory.isRegularMono_unop_iff_isRegularEpi** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：isRegularMono_unop_iff_isRegularEpi {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsRegularMon
o f.unop ↔ IsRegularEpi f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularMono.regularMono`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsR
egularMono f], Nonempty (Categ…
· 使用定理 `CategoryTheory.IsRegularEpi.regularEpi`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsReg
ularEpi f], Nonempty (Catego…
-/
lemma isRegularMono_unop_iff_isRegularEpi {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsRegularMono f.unop ↔ IsRegularEpi f :=
  ⟨fun hf ↦ ⟨⟨hf.regularMono.some.op⟩⟩, fun hf ↦ ⟨⟨hf.regularEpi.some.unop⟩⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsRegularEpi f] : IsRegularMono f.unop := by
  simpa

@[simp]
/-
**CategoryTheory.isRegularEpi_op_iff_isRegularMono** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isRegularEpi_op_iff_isRegularMono {X Y : C} (f : X ⟶ Y) : IsRegularEpi f.o
p ↔ IsRegularMono f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularEpi.regularEpi`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsReg
ularEpi f], Nonempty (Catego…
· 使用定理 `CategoryTheory.IsRegularMono.regularMono`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsR
egularMono f], Nonempty (Categ…
-/
lemma isRegularEpi_op_iff_isRegularMono {X Y : C} (f : X ⟶ Y) :
    IsRegularEpi f.op ↔ IsRegularMono f :=
  ⟨fun hf ↦ ⟨⟨hf.regularEpi.some.unop⟩⟩, fun hf ↦ ⟨⟨hf.regularMono.some.op⟩⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [IsRegularMono f] : IsRegularEpi f.op := by
  simpa

@[simp]
/-
**CategoryTheory.isRegularEpi_unop_iff_isRegularMono** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory`。
形式化陈述：isRegularEpi_unop_iff_isRegularMono {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsRegularEpi
 f.unop ↔ IsRegularMono f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularEpi.regularEpi`：∀ {C : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsReg
ularEpi f], Nonempty (Catego…
· 使用定理 `CategoryTheory.IsRegularMono.regularMono`：∀ {C : Type u₁} {inst : Catego
ryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y}   [self : CategoryTheory.IsR
egularMono f], Nonempty (Categ…
-/
lemma isRegularEpi_unop_iff_isRegularMono {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    IsRegularEpi f.unop ↔ IsRegularMono f :=
  ⟨fun hf ↦ ⟨⟨hf.regularEpi.some.op⟩⟩, fun hf ↦ ⟨⟨hf.regularMono.some.unop⟩⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsRegularMono f] : IsRegularEpi f.unop := by
  simpa

end

section

variable (C)

/-- A regular epi category is a category in which every epimorphism is regular. -/
/-
**CategoryTheory.IsRegularEpiCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A regular epi category is a category in which every epimorphism is regular.
-/
class IsRegularEpiCategory : Prop where
  /-- Everyone epimorphism is a regular epimorphism -/
  regularEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsRegularEpi f

end

/-- In a category in which every epimorphism is regular, we can express every epimorphism as
a coequalizer. This is not an instance because it would create an instance loop. -/
/-
**CategoryTheory.regularEpiOfEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：regularEpiOfEpi [IsRegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi 
f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsRegularEpiCategory.regularEpiOfEpi`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.IsRegularEpiCate
gory C] {X Y : C}   (f : X ⟶ Y) [Category…

--- 原说明 ---
In a category in which every epimorphism is regular, we can express every epimor
phism as
a coequalizer. This is not an instance because it would create an instance loop.
-/
def regularEpiOfEpi [IsRegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi f :=
  have := IsRegularEpiCategory.regularEpiOfEpi f
  IsRegularEpi.getStruct f
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) regularEpiCategoryOfSplitEpiCategory [SplitEpiCategory C] :
    IsRegularEpiCategory C where
  regularEpiOfEpi f _ := by
    have := isSplitEpi_of_epi f
    infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) strongEpiCategory_of_regularEpiCategory [IsRegularEpiCategory C] :
    StrongEpiCategory C where
  strongEpi_of_epi f _ := by
    have := isRegularEpi_of_regularEpi <| regularEpiOfEpi f
    infer_instance

end CategoryTheory

