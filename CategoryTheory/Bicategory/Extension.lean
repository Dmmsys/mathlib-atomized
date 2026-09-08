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

/-- Triangle diagrams for (left) extensions.
```
  b
  △ \
  |   \ extension  △
f |     \          | unit
  |       ◿
  a - - - ▷ c
      g
```
-/
/-
**CategoryTheory.Bicategory.LeftExtension** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：LeftExtension (f : a ⟶ b) (g : a ⟶ c)
参数：f : a ⟶ b；g : a ⟶ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Triangle diagrams for (left) extensions.
```
  b
  △ \
  |   \ extension  △
f |     \          | unit
  |       ◿
  a - - - ▷ c
      g
```
-/
abbrev LeftExtension (f : a ⟶ b) (g : a ⟶ c) := StructuredArrow g (precomp _ f)

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The extension of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.LeftExtension.extension** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：extension (t : LeftExtension f g) : b ⟶ c
参数：t : LeftExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of `g` along `f`.
-/
abbrev extension (t : LeftExtension f g) : b ⟶ c := t.right

/-- The 2-morphism filling the triangle diagram. -/
/-
**CategoryTheory.Bicategory.LeftExtension.unit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.Bicategory.LeftExtension`。
形式化陈述：unit (t : LeftExtension f g) : g ⟶ f ≫ t.extension
参数：t : LeftExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism filling the triangle diagram.
-/
abbrev unit (t : LeftExtension f g) : g ⟶ f ≫ t.extension := t.hom

/-- Construct a left extension from a 1-morphism and a 2-morphism. -/
/-
**CategoryTheory.Bicategory.LeftExtension.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Bicategory.LeftExtension`。
形式化陈述：mk (h : b ⟶ c) (unit : g ⟶ f ≫ h) : LeftExtension f g
参数：h : b ⟶ c；unit : g ⟶ f ≫ h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a left extension from a 1-morphism and a 2-morphism.
-/
abbrev mk (h : b ⟶ c) (unit : g ⟶ f ≫ h) : LeftExtension f g :=
  StructuredArrow.mk unit

variable {s t : LeftExtension f g}

/-- To construct a morphism between left extensions, we need a 2-morphism between the extensions,
and to check that it is compatible with the units. -/
/-
**CategoryTheory.Bicategory.LeftExtension.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.Bicategory.LeftExtension`。
形式化陈述：homMk (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit
参数：η : s.extension ⟶ t.extension。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct a morphism between left extensions, we need a 2-morphism between th
e extensions,
and to check that it is compatible with the units.
-/
abbrev homMk (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.LeftExtension.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Bicategory.LeftExtension`。
形式化陈述：w (η : s ⟶ t) : s.unit ≫ f ◁ η.right = t.unit
参数：η : s ⟶ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
-/
theorem w (η : s ⟶ t) : s.unit ≫ f ◁ η.right = t.unit :=
  StructuredArrow.w η

/-- The left extension along the identity. -/
/-
**CategoryTheory.Bicategory.LeftExtension.alongId** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Bicategory.LeftExtension`。
形式化陈述：alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g
参数：g : a ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left extension along the identity.
-/
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g := .mk _ (λ_ g).inv
/-
**CategoryTheory.Bicategory.LeftExtension.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Bicategory.LeftExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LeftExtension (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a left extension of `g : a ⟶ c` from a left extension of `g ≫ 𝟙 c`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.LeftExtension.ofCompId** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Bicategory.LeftExtension`。
形式化陈述：ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) : LeftExtension f g
参数：t : LeftExtension f (g ≫ 𝟙 c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a left extension of `g : a ⟶ c` from a left extension of `g ≫ 𝟙 c`.
-/
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) : LeftExtension f g :=
  mk (extension t) ((ρ_ g).inv ≫ unit t)

/-- Whisker a 1-morphism to an extension.
```
  b
  △ \
  |   \ extension  △
f |     \          | unit
  |       ◿
  a - - - ▷ c - - - ▷ x
      g         h
```
-/
/-
**CategoryTheory.Bicategory.LeftExtension.whisker** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Bicategory.LeftExtension`。
形式化陈述：whisker (t : LeftExtension f g) {x : B} (h : c ⟶ x) : LeftExtension f (g ≫
 h)
参数：t : LeftExtension f g；h : c ⟶ x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a 1-morphism to an extension.
```
  b
  △ \
  |   \ extension  △
f |     \          | unit
  |       ◿
  a - - - ▷ c - - - ▷ x
      g         h
```
-/
def whisker (t : LeftExtension f g) {x : B} (h : c ⟶ x) : LeftExtension f (g ≫ h) :=
  .mk _ <| t.unit ▷ h ≫ (α_ _ _ _).hom

@[simp]
/-
**CategoryTheory.Bicategory.LeftExtension.whisker_extension** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whisker_extension (t : LeftExtension f g) {x : B} (h : c ⟶ x) : (t.whisker
 h).extension = t.extension ≫ h
参数：t : LeftExtension f g；h : c ⟶ x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whisker_extension (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).extension = t.extension ≫ h :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.LeftExtension.whisker_unit** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whisker_unit (t : LeftExtension f g) {x : B} (h : c ⟶ x) : (t.whisker h).u
nit = t.unit ▷ h ≫ (α_ f t.extension h).hom
参数：t : LeftExtension f g；h : c ⟶ x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whisker_unit (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).unit = t.unit ▷ h ≫ (α_ f t.extension h).hom :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
/-
**CategoryTheory.Bicategory.LeftExtension.whiskering** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whiskering {x : B} (h : c ⟶ x) : LeftExtension f g ⥤ LeftExtension f (g ≫ 
h) where obj t
参数：h : c ⟶ x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 1-morphism is a functor.
-/
def whiskering {x : B} (h : c ⟶ x) : LeftExtension f g ⥤ LeftExtension f (g ≫ h) where
  obj t := t.whisker h
  map η := LeftExtension.homMk (η.right ▷ h) <| by
    simp [-LeftExtension.w, ← LeftExtension.w η]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between left extensions by cancelling the whiskered identities. -/
@[simps! right]
/-
**CategoryTheory.Bicategory.LeftExtension.whiskerIdCancel** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whiskerIdCancel (s : LeftExtension f (g ≫ 𝟙 c)) {t : LeftExtension f g} (τ
 : s ⟶ t.whisker (𝟙 c)) : s.ofCompId ⟶ t
参数：s : LeftExtension f (g ≫ 𝟙 c)；τ : s ⟶ t.whisker (𝟙 c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a morphism between left extensions by cancelling the whiskered identities
.
-/
def whiskerIdCancel
    (s : LeftExtension f (g ≫ 𝟙 c)) {t : LeftExtension f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofCompId ⟶ t :=
  LeftExtension.homMk (τ.right ≫ (ρ_ _).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered extensions. -/
@[simps! right]
/-
**CategoryTheory.Bicategory.LeftExtension.whiskerHom** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whiskerHom (i : s ⟶ t) {x : B} (h : c ⟶ x) : s.whisker h ⟶ t.whisker h
参数：i : s ⟶ t；h : c ⟶ x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between whiskered extensions.
-/
def whiskerHom (i : s ⟶ t) {x : B} (h : c ⟶ x) :
    s.whisker h ⟶ t.whisker h :=
  StructuredArrow.homMk (i.right ▷ h) <| by
    rw [← cancel_mono (α_ _ _ _).inv]
    calc
      _ = (unit s ≫ f ◁ i.right) ▷ h := by simp [-LeftExtension.w]
      _ = unit t ▷ h := congrArg (· ▷ h) (LeftExtension.w i)
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct an isomorphism between whiskered extensions. -/
/-
**CategoryTheory.Bicategory.LeftExtension.whiskerIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whiskerIso (i : s ≅ t) {x : B} (h : c ⟶ x) : s.whisker h ≅ t.whisker h
参数：i : s ≅ t；h : c ⟶ x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between whiskered extensions.
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
/-
**CategoryTheory.Bicategory.LeftExtension.whiskerOfCompIdIsoSelf** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Bicategory.LeftExtension`。
形式化陈述：whiskerOfCompIdIsoSelf (t : LeftExtension f g) : (t.whisker (𝟙 c)).ofCompI
d ≅ t
参数：t : LeftExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between left extensions induced by a right unitor.
-/
def whiskerOfCompIdIsoSelf (t : LeftExtension f g) : (t.whisker (𝟙 c)).ofCompId ≅ t :=
  StructuredArrow.isoMk (ρ_ (t.extension))

end LeftExtension

/-- Triangle diagrams for (left) lifts.
```
            b
          ◹ |
   lift /   |      △
      /     | f    | unit
    /       ▽
  c - - - ▷ a
       g
```
-/
/-
**CategoryTheory.Bicategory.LeftLift** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Bicategory`。
形式化陈述：LeftLift (f : b ⟶ a) (g : c ⟶ a)
参数：f : b ⟶ a；g : c ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Triangle diagrams for (left) lifts.
```
            b
          ◹ |
   lift /   |      △
      /     | f    | unit
    /       ▽
  c - - - ▷ a
       g
```
-/
abbrev LeftLift (f : b ⟶ a) (g : c ⟶ a) := StructuredArrow g (postcomp _ f)

namespace LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The lift of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.LeftLift.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Bicategory.LeftLift`。
形式化陈述：lift (t : LeftLift f g) : c ⟶ b
参数：t : LeftLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of `g` along `f`.
-/
abbrev lift (t : LeftLift f g) : c ⟶ b := t.right

/-- The 2-morphism filling the triangle diagram. -/
/-
**CategoryTheory.Bicategory.LeftLift.unit** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Bicategory.LeftLift`。
形式化陈述：unit (t : LeftLift f g) : g ⟶ t.lift ≫ f
参数：t : LeftLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism filling the triangle diagram.
-/
abbrev unit (t : LeftLift f g) : g ⟶ t.lift ≫ f := t.hom

/-- Construct a left lift from a 1-morphism and a 2-morphism. -/
/-
**CategoryTheory.Bicategory.LeftLift.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Bicategory.LeftLift`。
形式化陈述：mk (h : c ⟶ b) (unit : g ⟶ h ≫ f) : LeftLift f g
参数：h : c ⟶ b；unit : g ⟶ h ≫ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a left lift from a 1-morphism and a 2-morphism.
-/
abbrev mk (h : c ⟶ b) (unit : g ⟶ h ≫ f) : LeftLift f g :=
  StructuredArrow.mk unit

variable {s t : LeftLift f g}

/-- To construct a morphism between left lifts, we need a 2-morphism between the lifts,
and to check that it is compatible with the units. -/
/-
**CategoryTheory.Bicategory.LeftLift.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Bicategory.LeftLift`。
形式化陈述：homMk (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit
参数：η : s.lift ⟶ t.lift。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct a morphism between left lifts, we need a 2-morphism between the lif
ts,
and to check that it is compatible with the units.
-/
abbrev homMk (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.LeftLift.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Bicategory.LeftLift`。
形式化陈述：w (h : s ⟶ t) : s.unit ≫ h.right ▷ f = t.unit
参数：h : s ⟶ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
-/
theorem w (h : s ⟶ t) : s.unit ≫ h.right ▷ f = t.unit :=
  StructuredArrow.w h

/-- The left lift along the identity. -/
/-
**CategoryTheory.Bicategory.LeftLift.alongId** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Bicategory.LeftLift`。
形式化陈述：alongId (g : c ⟶ a) : LeftLift (𝟙 a) g
参数：g : c ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left lift along the identity.
-/
def alongId (g : c ⟶ a) : LeftLift (𝟙 a) g := .mk _ (ρ_ g).inv
/-
**CategoryTheory.Bicategory.LeftLift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Bicategory.LeftLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (LeftLift (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a left lift along `g : c ⟶ a` from a left lift along `𝟙 c ≫ g`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.LeftLift.ofIdComp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Bicategory.LeftLift`。
形式化陈述：ofIdComp (t : LeftLift f (𝟙 c ≫ g)) : LeftLift f g
参数：t : LeftLift f (𝟙 c ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a left lift along `g : c ⟶ a` from a left lift along `𝟙 c ≫ g`.
-/
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) : LeftLift f g :=
  mk (lift t) ((λ_ _).inv ≫ unit t)

/-- Whisker a 1-morphism to a lift.
```
                    b
                  ◹ |
           lift /   |      △
              /     | f    | unit
            /       ▽
x - - - ▷ c - - - ▷ a
     h         g
```
-/
/-
**CategoryTheory.Bicategory.LeftLift.whisker** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Bicategory.LeftLift`。
形式化陈述：whisker (t : LeftLift f g) {x : B} (h : x ⟶ c) : LeftLift f (h ≫ g)
参数：t : LeftLift f g；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a 1-morphism to a lift.
```
                    b
                  ◹ |
           lift /   |      △
              /     | f    | unit
            /       ▽
x - - - ▷ c - - - ▷ a
     h         g
```
-/
def whisker (t : LeftLift f g) {x : B} (h : x ⟶ c) : LeftLift f (h ≫ g) :=
  .mk _ <| h ◁ t.unit ≫ (α_ _ _ _).inv

@[simp]
/-
**CategoryTheory.Bicategory.LeftLift.whisker_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory.LeftLift`。
形式化陈述：whisker_lift (t : LeftLift f g) {x : B} (h : x ⟶ c) : (t.whisker h).lift =
 h ≫ t.lift
参数：t : LeftLift f g；h : x ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whisker_lift (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).lift = h ≫ t.lift :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.LeftLift.whisker_unit** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory.LeftLift`。
形式化陈述：whisker_unit (t : LeftLift f g) {x : B} (h : x ⟶ c) : (t.whisker h).unit =
 h ◁ t.unit ≫ (α_ h t.lift f).inv
参数：t : LeftLift f g；h : x ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whisker_unit (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).unit = h ◁ t.unit ≫ (α_ h t.lift f).inv :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
/-
**CategoryTheory.Bicategory.LeftLift.whiskering** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory.LeftLift`。
形式化陈述：whiskering {x : B} (h : x ⟶ c) : LeftLift f g ⥤ LeftLift f (h ≫ g) where o
bj t
参数：h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 1-morphism is a functor.
-/
def whiskering {x : B} (h : x ⟶ c) : LeftLift f g ⥤ LeftLift f (h ≫ g) where
  obj t := t.whisker h
  map η := LeftLift.homMk (h ◁ η.right) <| by
    dsimp only [whisker_lift, whisker_unit]
    rw [← LeftLift.w η]
    simp [-LeftLift.w]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between left lifts by cancelling the whiskered identities. -/
@[simps! right]
/-
**CategoryTheory.Bicategory.LeftLift.whiskerIdCancel** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Bicategory.LeftLift`。
形式化陈述：whiskerIdCancel (s : LeftLift f (𝟙 c ≫ g)) {t : LeftLift f g} (τ : s ⟶ t.w
hisker (𝟙 c)) : s.ofIdComp ⟶ t
参数：s : LeftLift f (𝟙 c ≫ g)；τ : s ⟶ t.whisker (𝟙 c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a morphism between left lifts by cancelling the whiskered identities.
-/
def whiskerIdCancel
    (s : LeftLift f (𝟙 c ≫ g)) {t : LeftLift f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofIdComp ⟶ t :=
  LeftLift.homMk (τ.right ≫ (λ_ _).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered lifts. -/
@[simps! right]
/-
**CategoryTheory.Bicategory.LeftLift.whiskerHom** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory.LeftLift`。
形式化陈述：whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) : s.whisker h ⟶ t.whisker h
参数：i : s ⟶ t；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between whiskered lifts.
-/
def whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) :
    s.whisker h ⟶ t.whisker h :=
  StructuredArrow.homMk (h ◁ i.right) <| by
    rw [← cancel_mono (α_ h _ _).hom]
    calc
      _ = h ◁ (unit s ≫ i.right ▷ f) := by simp [-LeftLift.w]
      _ = h ◁ unit t := congrArg (h ◁ ·) (LeftLift.w i)
      _ = _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct an isomorphism between whiskered lifts. -/
/-
**CategoryTheory.Bicategory.LeftLift.whiskerIso** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Bicategory.LeftLift`。
形式化陈述：whiskerIso (i : s ≅ t) {x : B} (h : x ⟶ c) : s.whisker h ≅ t.whisker h
参数：i : s ≅ t；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between whiskered lifts.
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
/-
**CategoryTheory.Bicategory.LeftLift.whiskerOfIdCompIsoSelf** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Bicategory.LeftLift`。
形式化陈述：whiskerOfIdCompIsoSelf (t : LeftLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t
参数：t : LeftLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between left lifts induced by a left unitor.
-/
def whiskerOfIdCompIsoSelf (t : LeftLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  StructuredArrow.isoMk (λ_ (lift t))

end LeftLift

/-- Triangle diagrams for (right) extensions.
```
  b
  △ \
  |   \ extension  | counit
f |     \          ▽
  |       ◿
  a - - - ▷ c
      g
```
-/
/-
**CategoryTheory.Bicategory.RightExtension** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：RightExtension (f : a ⟶ b) (g : a ⟶ c)
参数：f : a ⟶ b；g : a ⟶ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Triangle diagrams for (right) extensions.
```
  b
  △ \
  |   \ extension  | counit
f |     \          ▽
  |       ◿
  a - - - ▷ c
      g
```
-/
abbrev RightExtension (f : a ⟶ b) (g : a ⟶ c) := CostructuredArrow (precomp _ f) g

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The extension of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.RightExtension.extension** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.Bicategory.RightExtension`。
形式化陈述：extension (t : RightExtension f g) : b ⟶ c
参数：t : RightExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of `g` along `f`.
-/
abbrev extension (t : RightExtension f g) : b ⟶ c := t.left

/-- The 2-morphism filling the triangle diagram. -/
/-
**CategoryTheory.Bicategory.RightExtension.counit** 是 Mathlib 中的一个缩写定义，位于命名空间 `C
ategoryTheory.Bicategory.RightExtension`。
形式化陈述：counit (t : RightExtension f g) : f ≫ t.extension ⟶ g
参数：t : RightExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism filling the triangle diagram.
-/
abbrev counit (t : RightExtension f g) : f ≫ t.extension ⟶ g := t.hom

/-- Construct a right extension from a 1-morphism and a 2-morphism. -/
/-
**CategoryTheory.Bicategory.RightExtension.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Bicategory.RightExtension`。
形式化陈述：mk (h : b ⟶ c) (counit : f ≫ h ⟶ g) : RightExtension f g
参数：h : b ⟶ c；counit : f ≫ h ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a right extension from a 1-morphism and a 2-morphism.
-/
abbrev mk (h : b ⟶ c) (counit : f ≫ h ⟶ g) : RightExtension f g :=
  CostructuredArrow.mk counit

/-- To construct a morphism between right extensions, we need a 2-morphism between the extensions,
and to check that it is compatible with the counits. -/
/-
**CategoryTheory.Bicategory.RightExtension.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Bicategory.RightExtension`。
形式化陈述：homMk {s t : RightExtension f g} (η : s.extension ⟶ t.extension) (w : f ◁ 
η ≫ t.counit = s.counit
参数：η : s.extension ⟶ t.extension。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct a morphism between right extensions, we need a 2-morphism between t
he extensions,
and to check that it is compatible with the counits.
-/
abbrev homMk {s t : RightExtension f g} (η : s.extension ⟶ t.extension)
    (w : f ◁ η ≫ t.counit = s.counit := by cat_disch) : s ⟶ t :=
  CostructuredArrow.homMk η w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.RightExtension.w** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory.RightExtension`。
形式化陈述：w {s t : RightExtension f g} (η : s ⟶ t) : f ◁ η.left ≫ t.counit = s.couni
t
参数：η : s ⟶ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
-/
theorem w {s t : RightExtension f g} (η : s ⟶ t) :
    f ◁ η.left ≫ t.counit = s.counit :=
  CostructuredArrow.w η

/-- The right extension along the identity. -/
/-
**CategoryTheory.Bicategory.RightExtension.alongId** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Bicategory.RightExtension`。
形式化陈述：alongId (g : a ⟶ c) : RightExtension (𝟙 a) g
参数：g : a ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right extension along the identity.
-/
def alongId (g : a ⟶ c) : RightExtension (𝟙 a) g := .mk _ (λ_ g).hom
/-
**CategoryTheory.Bicategory.RightExtension.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Bicategory.RightExtension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RightExtension (𝟙 a) g) := ⟨alongId g⟩

end RightExtension

/-- Triangle diagrams for (right) lifts.
```
            b
          ◹ |
   lift /   |      | counit
      /     | f    ▽
    /       ▽
  c - - - ▷ a
       g
```
-/
/-
**CategoryTheory.Bicategory.RightLift** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Bicategory`。
形式化陈述：RightLift (f : b ⟶ a) (g : c ⟶ a)
参数：f : b ⟶ a；g : c ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Triangle diagrams for (right) lifts.
```
            b
          ◹ |
   lift /   |      | counit
      /     | f    ▽
    /       ▽
  c - - - ▷ a
       g
```
-/
abbrev RightLift (f : b ⟶ a) (g : c ⟶ a) := CostructuredArrow (postcomp _ f) g

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The lift of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.RightLift.lift** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Bicategory.RightLift`。
形式化陈述：lift (t : RightLift f g) : c ⟶ b
参数：t : RightLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lift of `g` along `f`.
-/
abbrev lift (t : RightLift f g) : c ⟶ b := t.left

/-- The 2-morphism filling the triangle diagram. -/
/-
**CategoryTheory.Bicategory.RightLift.counit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Bicategory.RightLift`。
形式化陈述：counit (t : RightLift f g) : t.lift ≫ f ⟶ g
参数：t : RightLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-morphism filling the triangle diagram.
-/
abbrev counit (t : RightLift f g) : t.lift ≫ f ⟶ g := t.hom

/-- Construct a right lift from a 1-morphism and a 2-morphism. -/
/-
**CategoryTheory.Bicategory.RightLift.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Bicategory.RightLift`。
形式化陈述：mk (h : c ⟶ b) (counit : h ≫ f ⟶ g) : RightLift f g
参数：h : c ⟶ b；counit : h ≫ f ⟶ g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a right lift from a 1-morphism and a 2-morphism.
-/
abbrev mk (h : c ⟶ b) (counit : h ≫ f ⟶ g) : RightLift f g :=
  CostructuredArrow.mk counit

variable {s t : RightLift f g}

/-- To construct a morphism between right lifts, we need a 2-morphism between the lifts,
and to check that it is compatible with the counits. -/
/-
**CategoryTheory.Bicategory.RightLift.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Bicategory.RightLift`。
形式化陈述：homMk (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit
参数：η : s.lift ⟶ t.lift。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct a morphism between right lifts, we need a 2-morphism between the li
fts,
and to check that it is compatible with the counits.
-/
abbrev homMk (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit := by cat_disch) :
    s ⟶ t :=
  CostructuredArrow.homMk η w

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.RightLift.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Bicategory.RightLift`。
形式化陈述：w (h : s ⟶ t) : h.left ▷ f ≫ t.counit = s.counit
参数：h : s ⟶ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
-/
theorem w (h : s ⟶ t) : h.left ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.w h

/-- The right lift along the identity. -/
/-
**CategoryTheory.Bicategory.RightLift.alongId** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Bicategory.RightLift`。
形式化陈述：alongId (g : c ⟶ a) : RightLift (𝟙 a) g
参数：g : c ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right lift along the identity.
-/
def alongId (g : c ⟶ a) : RightLift (𝟙 a) g := .mk _ (ρ_ g).hom
/-
**CategoryTheory.Bicategory.RightLift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Bicategory.RightLift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RightLift (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a right lift along `g : c ⟶ a` from a right lift along `𝟙 c ≫ g`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.RightLift.ofIdComp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Bicategory.RightLift`。
形式化陈述：ofIdComp (t : RightLift f (𝟙 c ≫ g)) : RightLift f g
参数：t : RightLift f (𝟙 c ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a right lift along `g : c ⟶ a` from a right lift along `𝟙 c ≫ g`.
-/
def ofIdComp (t : RightLift f (𝟙 c ≫ g)) : RightLift f g :=
  mk (lift t) (counit t ≫ (λ_ _).hom)

/-- Whisker a 1-morphism to a lift.
```
                    b
                  ◹ |
           lift /   |      | counit
              /     | f    ▽
            /       ▽
x - - - ▷ c - - - ▷ a
     h         g
```
-/
/-
**CategoryTheory.Bicategory.RightLift.whisker** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Bicategory.RightLift`。
形式化陈述：whisker (t : RightLift f g) {x : B} (h : x ⟶ c) : RightLift f (h ≫ g)
参数：t : RightLift f g；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whisker a 1-morphism to a lift.
```
                    b
                  ◹ |
           lift /   |      | counit
              /     | f    ▽
            /       ▽
x - - - ▷ c - - - ▷ a
     h         g
```
-/
def whisker (t : RightLift f g) {x : B} (h : x ⟶ c) : RightLift f (h ≫ g) :=
  .mk _ <| (α_ _ _ _).hom ≫ h ◁ t.counit

@[simp]
/-
**CategoryTheory.Bicategory.RightLift.whisker_lift** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Bicategory.RightLift`。
形式化陈述：whisker_lift (t : RightLift f g) {x : B} (h : x ⟶ c) : (t.whisker h).lift 
= h ≫ t.lift
参数：t : RightLift f g；h : x ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whisker_lift (t : RightLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).lift = h ≫ t.lift :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.RightLift.whisker_counit** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Bicategory.RightLift`。
形式化陈述：whisker_counit (t : RightLift f g) {x : B} (h : x ⟶ c) : (t.whisker h).cou
nit = (α_ h t.lift f).hom ≫ h ◁ t.counit
参数：t : RightLift f g；h : x ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whisker_counit (t : RightLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).counit = (α_ h t.lift f).hom ≫ h ◁ t.counit :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
/-
**CategoryTheory.Bicategory.RightLift.whiskering** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Bicategory.RightLift`。
形式化陈述：whiskering {x : B} (h : x ⟶ c) : RightLift f g ⥤ RightLift f (h ≫ g) where
 obj t
参数：h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 1-morphism is a functor.
-/
def whiskering {x : B} (h : x ⟶ c) : RightLift f g ⥤ RightLift f (h ≫ g) where
  obj t := t.whisker h
  map η := RightLift.homMk (h ◁ η.left) <| by
    dsimp only [whisker_lift, whisker_counit]
    rw [← RightLift.w η]
    simp [-RightLift.w]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between right lifts by cancelling the whiskered identities. -/
@[simps! left]
/-
**CategoryTheory.Bicategory.RightLift.whiskerIdCancel** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Bicategory.RightLift`。
形式化陈述：whiskerIdCancel (t : RightLift f (𝟙 c ≫ g)) {s : RightLift f g} (τ : s.whi
sker (𝟙 c) ⟶ t) : s ⟶ t.ofIdComp
参数：t : RightLift f (𝟙 c ≫ g)；τ : s.whisker (𝟙 c) ⟶ t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a morphism between right lifts by cancelling the whiskered identities.
-/
def whiskerIdCancel
    (t : RightLift f (𝟙 c ≫ g)) {s : RightLift f g} (τ : s.whisker (𝟙 c) ⟶ t) :
    s ⟶ t.ofIdComp :=
  RightLift.homMk ((λ_ _).inv ≫ τ.left)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered lifts. -/
@[simps! left]
/-
**CategoryTheory.Bicategory.RightLift.whiskerHom** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Bicategory.RightLift`。
形式化陈述：whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) : s.whisker h ⟶ t.whisker h
参数：i : s ⟶ t；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between whiskered lifts.
-/
def whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) :
    s.whisker h ⟶ t.whisker h :=
  CostructuredArrow.homMk (h ◁ i.left) <| by
    rw [← cancel_epi (α_ h _ _).inv]
    calc
      _ = h ◁ (i.left ▷ f ≫ t.counit) := by simp [-RightLift.w]
      _ = h ◁ s.counit := congrArg (h ◁ ·) (RightLift.w i)
      _ = _ := by simp

/-- Construct an isomorphism between whiskered lifts. -/
/-
**CategoryTheory.Bicategory.RightLift.whiskerIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Bicategory.RightLift`。
形式化陈述：whiskerIso (i : s ≅ t) {x : B} (h : x ⟶ c) : s.whisker h ≅ t.whisker h
参数：i : s ≅ t；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between whiskered lifts.
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
/-
**CategoryTheory.Bicategory.RightLift.whiskerOfIdCompIsoSelf** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Bicategory.RightLift`。
形式化陈述：whiskerOfIdCompIsoSelf (t : RightLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ 
t
参数：t : RightLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between right lifts induced by a left unitor.
-/
def whiskerOfIdCompIsoSelf (t : RightLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  CostructuredArrow.isoMk (λ_ (lift t))

end RightLift

end Bicategory

end CategoryTheory

