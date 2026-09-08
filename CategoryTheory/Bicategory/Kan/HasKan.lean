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

/-- The existence of a left Kan extension of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.HasLeftKanExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：{B : Type u} → [inst : CategoryTheory.Bicategory B] → {a b c : B} → (a ⟶ b
) → (a ⟶ c) → Prop
参数：a ⟶ b；a ⟶ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The existence of a left Kan extension of `g` along `f`.
-/
class HasLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop where
  hasInitial : HasInitial <| LeftExtension f g
/-
**CategoryTheory.Bicategory.LeftExtension.IsKan.hasLeftKanExtension** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsKan`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b
} {g : a ⟶ c}   {t : CategoryTheory.Bicategory.LeftExtension f g} (H : t.IsKan),
 CategoryTheory.Bicategory.HasLeftKanExtension f g
参数：H : t.IsKan。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
-/
theorem LeftExtension.IsKan.hasLeftKanExtension {t : LeftExtension f g} (H : IsKan t) :
    HasLeftKanExtension f g :=
  ⟨IsInitial.hasInitial H⟩
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLeftKanExtension f g] : HasInitial <| LeftExtension f g :=
  HasLeftKanExtension.hasInitial

/-- The left Kan extension of `g` along `f` at the level of structured arrows. -/
/-
**CategoryTheory.Bicategory.lanLeftExtension** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：lanLeftExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftE
xtension f g
参数：f : a ⟶ b；g : a ⟶ c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instHasInitialLeftExtensionOfHasLeftKanExtensi
on`：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b} 
{g : a ⟶ c}   [CategoryTheory.Bicategory.HasLeftKanExtension f g…

--- 原说明 ---
The left Kan extension of `g` along `f` at the level of structured arrows.
-/
def lanLeftExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftExtension f g :=
  ⊥_ (LeftExtension f g)

/-- The left Kan extension of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.lan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bicate
gory`。
形式化陈述：lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c
参数：f : a ⟶ b；g : a ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left Kan extension of `g` along `f`.
-/
def lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c :=
  (lanLeftExtension f g).extension

/-- `f⁺ g` is the left Kan extension of `g` along `f`.
```
  b
  △ \
  |   \ f⁺ g
f |     \
  |       ◿
  a - - - ▷ c
      g
```
-/
scoped infixr:90 "⁺ " => lan

@[simp]
/-
**CategoryTheory.Bicategory.lanLeftExtension_extension** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Bicategory`。
形式化陈述：lanLeftExtension_extension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f 
g] : (lanLeftExtension f g).extension = f⁺ g
参数：f : a ⟶ b；g : a ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lanLeftExtension_extension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (lanLeftExtension f g).extension = f⁺ g := rfl

/-- The unit for the left Kan extension `f⁺ g`. -/
/-
**CategoryTheory.Bicategory.lanUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bi
category`。
形式化陈述：lanUnit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : g ⟶ f ≫ f⁺ g
参数：f : a ⟶ b；g : a ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the left Kan extension `f⁺ g`.
-/
def lanUnit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : g ⟶ f ≫ f⁺ g :=
  (lanLeftExtension f g).unit

@[simp]
/-
**CategoryTheory.Bicategory.lanLeftExtension_unit** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Bicategory`。
形式化陈述：lanLeftExtension_unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : 
(lanLeftExtension f g).unit = lanUnit f g
参数：f : a ⟶ b；g : a ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lanLeftExtension_unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (lanLeftExtension f g).unit = lanUnit f g := rfl

/-- Evidence that `lanLeftExtension f g` is a Kan extension. -/
/-
**CategoryTheory.Bicategory.lanIsKan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
icategory`。
形式化陈述：lanIsKan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : (lanLeftExten
sion f g).IsKan
参数：f : a ⟶ b；g : a ⟶ c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instHasInitialLeftExtensionOfHasLeftKanExtensi
on`：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b} 
{g : a ⟶ c}   [CategoryTheory.Bicategory.HasLeftKanExtension f g…

--- 原说明 ---
Evidence that `lanLeftExtension f g` is a Kan extension.
-/
def lanIsKan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : (lanLeftExtension f g).IsKan :=
  initialIsInitial

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The family of 2-morphisms out of the left Kan extension `f⁺ g`. -/
/-
**CategoryTheory.Bicategory.lanDesc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bi
category`。
形式化陈述：lanDesc [HasLeftKanExtension f g] (s : LeftExtension f g) : f⁺ g ⟶ s.exten
sion
参数：s : LeftExtension f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms out of the left Kan extension `f⁺ g`.
-/
def lanDesc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    f⁺ g ⟶ s.extension :=
  (lanIsKan f g).desc s

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.lanUnit_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Bicategory`。
形式化陈述：lanUnit_desc [HasLeftKanExtension f g] (s : LeftExtension f g) : lanUnit f
 g ≫ f ◁ lanDesc s = s.unit
参数：s : LeftExtension f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LeftExtension.IsKan.fac`：fac (H : IsKan t) (s 
: LeftExtension f g) : t.unit ≫ f ◁ H.desc s = s.unit
-/
theorem lanUnit_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    lanUnit f g ≫ f ◁ lanDesc s = s.unit :=
  (lanIsKan f g).fac s

@[simp]
/-
**CategoryTheory.Bicategory.lanIsKan_desc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Bicategory`。
形式化陈述：lanIsKan_desc [HasLeftKanExtension f g] (s : LeftExtension f g) : (lanIsKa
n f g).desc s = lanDesc s
参数：s : LeftExtension f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lanIsKan_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    (lanIsKan f g).desc s = lanDesc s :=
  rfl
/-
**CategoryTheory.Bicategory.Lan.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory.Lan`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b
} {g : a ⟶ c}   [inst_1 : CategoryTheory.Bicategory.HasLeftKanExtension f g] (s 
: CategoryTheory.Bicategory.LeftExtension f g),   ∃! τ,     CategoryTheory.Categ
oryStruct.comp (CategoryTheory.Bicategory.lanUnit f g)         (CategoryTheory.B
icategory.whiskerLeft f τ) =       s.unit
参数：s : CategoryTheory.Bicategory.LeftExtension f g；CategoryTheory.Bicategory.lan
Unit f g；CategoryTheory.Bicategory.whiskerLeft f τ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.existsUnique`：existsUnique (h
 : IsUniversal f) (g : StructuredArrow S T) : exists! η : f.right ⟶ g.right, f.h
om ≫ T.map η = g.hom
-/
theorem Lan.existsUnique [HasLeftKanExtension f g] (s : LeftExtension f g) :
    ∃! τ, lanUnit f g ≫ f ◁ τ = s.unit :=
  (lanIsKan f g).existsUnique _

/-- We say that a 1-morphism `h` commutes with the left Kan extension `f⁺ g` if the whiskered
left extension for `f⁺ g` by `h` is a Kan extension of `g ≫ h` along `f`. -/
/-
**CategoryTheory.Bicategory.Lan.CommuteWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.Bicategory.Lan`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c : B} → 
      (f : a ⟶ b) → (g : a ⟶ c) → [CategoryTheory.Bicategory.HasLeftKanExtension
 f g] → {x : B} → (c ⟶ x) → Prop
参数：f : a ⟶ b；g : a ⟶ c；c ⟶ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a 1-morphism `h` commutes with the left Kan extension `f⁺ g` if the 
whiskered
left extension for `f⁺ g` by `h` is a Kan extension of `g ≫ h` along `f`.
-/
class Lan.CommuteWith
    (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] {x : B} (h : c ⟶ x) : Prop where
  commute : Nonempty <| IsKan <| (lanLeftExtension f g).whisker h

namespace Lan.CommuteWith

/-
**CategoryTheory.Bicategory.Lan.CommuteWith.of_isKan_whisker** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：of_isKan_whisker [HasLeftKanExtension f g] (t : LeftExtension f g) {x : B}
 (h : c ⟶ x) (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLeftExtension f g)
.whisker h) : Lan.CommuteWith f g h
参数：t : LeftExtension f g；h : c ⟶ x；H : IsKan (t.whisker h)；i : t.whisker h ≅ (la
nLeftExtension f g).whisker h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_isKan_whisker [HasLeftKanExtension f g] (t : LeftExtension f g) {x : B} (h : c ⟶ x)
    (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLeftExtension f g).whisker h) :
    Lan.CommuteWith f g h :=
  ⟨⟨IsKan.ofIsoKan H i⟩⟩
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.of_lan_comp_iso** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：of_lan_comp_iso [HasLeftKanExtension f g] {x : B} {h : c ⟶ x} [HasLeftKanE
xtension f (g ≫ h)] (i : f⁺ (g ≫ h) ≅ f⁺ g ≫ h) (w : lanUnit f (g ≫ h) ≫ f ◁ i.h
om = lanUnit f g ▷ h ≫ (α_ _ _ _).hom) : Lan.CommuteWith f g h
参数：g ≫ h；i : f⁺ (g ≫ h) ≅ f⁺ g ≫ h；w : lanUnit f (g ≫ h) ≫ f ◁ i.hom = lanUnit f
 g ▷ h ≫ (α_ _ _ _).hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.precomp_map`：∀ {B : Type u} [inst : CategoryTh
eory.Bicategory B] {a b : B} (c : B) (f : a ⟶ b) {X Y : b ⟶ c} (x : X ⟶ Y),   (C
ategoryTheory.Bicategory.pr…
-/
theorem of_lan_comp_iso [HasLeftKanExtension f g]
    {x : B} {h : c ⟶ x} [HasLeftKanExtension f (g ≫ h)]
    (i : f⁺ (g ≫ h) ≅ f⁺ g ≫ h)
    (w : lanUnit f (g ≫ h) ≫ f ◁ i.hom = lanUnit f g ▷ h ≫ (α_ _ _ _).hom) :
    Lan.CommuteWith f g h :=
  ⟨⟨(lanIsKan f (g ≫ h)).ofIsoKan <| StructuredArrow.isoMk i⟩⟩

variable (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
variable {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h]

/-- Evidence that `h` commutes with the left Kan extension `f⁺ g`. -/
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.isKan** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：isKan : IsKan (lanLeftExtension f g).whisker h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.Lan.CommuteWith.commute`：∀ {B : Type u} {inst 
: CategoryTheory.Bicategory B} {a b c : B} {f : a ⟶ b} {g : a ⟶ c}   {inst_1 : C
ategoryTheory.Bicategory.HasLeftKanExte…

--- 原说明 ---
Evidence that `h` commutes with the left Kan extension `f⁺ g`.
-/
def isKan : IsKan <| (lanLeftExtension f g).whisker h := Classical.choice Lan.CommuteWith.commute
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Bicategory.Lan.CommuteWith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLeftKanExtension f (g ≫ h) := (Lan.CommuteWith.isKan f g h).hasLeftKanExtension

/-- If `h` commutes with `f⁺ g` and `t` is another left Kan extension of `g` along `f`, then
`t.whisker h` is a left Kan extension of `g ≫ h` along `f`. -/
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.isKanWhisker** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：isKanWhisker (t : LeftExtension f g) (H : IsKan t) {x : B} (h : c ⟶ x) [La
n.CommuteWith f g h] : IsKan (t.whisker h)
参数：t : LeftExtension f g；H : IsKan t；h : c ⟶ x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h` commutes with `f⁺ g` and `t` is another left Kan extension of `g` along `
f`, then
`t.whisker h` is a left Kan extension of `g ≫ h` along `f`.
-/
def isKanWhisker
    (t : LeftExtension f g) (H : IsKan t) {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h] :
    IsKan (t.whisker h) :=
  IsKan.whiskerOfCommute (lanLeftExtension f g) t (IsKan.uniqueUpToIso (lanIsKan f g) H) h
    (isKan f g h)

/-- The isomorphism `f⁺ (g ≫ h) ≅ f⁺ g ≫ h` at the level of structured arrows. -/
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.lanCompIsoWhisker** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：lanCompIsoWhisker : lanLeftExtension f (g ≫ h) ≅ (lanLeftExtension f g).wh
isker h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.Lan.CommuteWith.instHasLeftKanExtensionComp`：∀
 {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : 
a ⟶ c)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanExte…

--- 原说明 ---
The isomorphism `f⁺ (g ≫ h) ≅ f⁺ g ≫ h` at the level of structured arrows.
-/
def lanCompIsoWhisker : lanLeftExtension f (g ≫ h) ≅ (lanLeftExtension f g).whisker h :=
  IsKan.uniqueUpToIso (lanIsKan f (g ≫ h)) (Lan.CommuteWith.isKan f g h)

@[simp]
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.lanCompIsoWhisker_hom_right** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：lanCompIsoWhisker_hom_right : (lanCompIsoWhisker f g h).hom.right = lanDes
c ((lanLeftExtension f g).whisker h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.Lan.CommuteWith.instHasLeftKanExtensionComp`：∀
 {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : 
a ⟶ c)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanExte…
-/
theorem lanCompIsoWhisker_hom_right :
    (lanCompIsoWhisker f g h).hom.right = lanDesc ((lanLeftExtension f g).whisker h) :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.lanCompIsoWhisker_inv_right** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：lanCompIsoWhisker_inv_right : (lanCompIsoWhisker f g h).inv.right = (isKan
 f g h).desc (lanLeftExtension f (g ≫ h))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.Lan.CommuteWith.instHasLeftKanExtensionComp`：∀
 {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : 
a ⟶ c)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanExte…
-/
theorem lanCompIsoWhisker_inv_right :
    (lanCompIsoWhisker f g h).inv.right = (isKan f g h).desc (lanLeftExtension f (g ≫ h)) :=
  rfl

/-- The 1-morphism `h` commutes with the left Kan extension `f⁺ g`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.Lan.CommuteWith.lanCompIso** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Bicategory.Lan.CommuteWith`。
形式化陈述：lanCompIso : f⁺ (g ≫ h) ≅ f⁺ g ≫ h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.Lan.CommuteWith.instHasLeftKanExtensionComp`：∀
 {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : a ⟶ b) (g : 
a ⟶ c)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanExte…

--- 原说明 ---
The 1-morphism `h` commutes with the left Kan extension `f⁺ g`.
-/
def lanCompIso : f⁺ (g ≫ h) ≅ f⁺ g ≫ h := Comma.rightIso <| lanCompIsoWhisker f g h

end Lan.CommuteWith

/-- We say that there exists an absolute left Kan extension of `g` along `f` if any 1-morphism `h`
commutes with the left Kan extension `f⁺ g`. -/
/-
**CategoryTheory.Bicategory.HasAbsLeftKanExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Bicategory`。
形式化陈述：{B : Type u} → [inst : CategoryTheory.Bicategory B] → {a b c : B} → (a ⟶ b
) → (a ⟶ c) → Prop
参数：a ⟶ b；a ⟶ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that there exists an absolute left Kan extension of `g` along `f` if any 
1-morphism `h`
commutes with the left Kan extension `f⁺ g`.
-/
class HasAbsLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop extends HasLeftKanExtension f g where
  commute {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasAbsLeftKanExtension f g] {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h :=
  HasAbsLeftKanExtension.commute h
/-
**CategoryTheory.Bicategory.LeftExtension.IsAbsKan.hasAbsLeftKanExtension** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LeftExtension.IsAbsKan`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b
} {g : a ⟶ c}   {t : CategoryTheory.Bicategory.LeftExtension f g} (H : t.IsAbsKa
n),   CategoryTheory.Bicategory.HasAbsLeftKanExtension f g
参数：H : t.IsAbsKan。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LeftExtension.IsKan.hasLeftKanExtension`：∀ {B 
: Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : a ⟶ b} {g : a ⟶ 
c}   {t : CategoryTheory.Bicategory.LeftExtension f g} …
-/
theorem LeftExtension.IsAbsKan.hasAbsLeftKanExtension {t : LeftExtension f g} (H : IsAbsKan t) :
    HasAbsLeftKanExtension f g :=
  have : HasLeftKanExtension f g := H.isKan.hasLeftKanExtension
  ⟨fun h ↦ ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanIsKan f g)) h⟩⟩⟩

end LeftKan

section LeftLift

open LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The existence of a left Kan lift of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.HasLeftKanLift** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：{B : Type u} → [inst : CategoryTheory.Bicategory B] → {a b c : B} → (b ⟶ a
) → (c ⟶ a) → Prop
参数：b ⟶ a；c ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The existence of a left Kan lift of `g` along `f`.
-/
class HasLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop where mk' ::
  hasInitial : HasInitial <| LeftLift f g
/-
**CategoryTheory.Bicategory.LeftLift.IsKan.hasLeftKanLift** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Bicategory.LeftLift.IsKan`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : b ⟶ a
} {g : c ⟶ a}   {t : CategoryTheory.Bicategory.LeftLift f g} (H : t.IsKan), Cate
goryTheory.Bicategory.HasLeftKanLift f g
参数：H : t.IsKan。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
-/
theorem LeftLift.IsKan.hasLeftKanLift {t : LeftLift f g} (H : IsKan t) : HasLeftKanLift f g :=
  ⟨IsInitial.hasInitial H⟩
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLeftKanLift f g] : HasInitial <| LeftLift f g := HasLeftKanLift.hasInitial

/-- The left Kan lift of `g` along `f` at the level of structured arrows. -/
/-
**CategoryTheory.Bicategory.lanLiftLeftLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Bicategory`。
形式化陈述：lanLiftLeftLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftLift f 
g
参数：f : b ⟶ a；g : c ⟶ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instHasInitialLeftLiftOfHasLeftKanLift`：∀ {B :
 Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : b ⟶ a} {g : c ⟶ a
}   [CategoryTheory.Bicategory.HasLeftKanLift f g],   …

--- 原说明 ---
The left Kan lift of `g` along `f` at the level of structured arrows.
-/
def lanLiftLeftLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftLift f g :=
  ⊥_ (LeftLift f g)

/-- The left Kan lift of `g` along `f`. -/
/-
**CategoryTheory.Bicategory.lanLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Bi
category`。
形式化陈述：lanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : c ⟶ b
参数：f : b ⟶ a；g : c ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left Kan lift of `g` along `f`.
-/
def lanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : c ⟶ b :=
  (lanLiftLeftLift f g).lift

/-- `f₊ g` is the left Kan lift of `g` along `f`.
```
            b
          ◹ |
   f₊ g /   |
      /     | f
    /       ▽
  c - - - ▷ a
       g
```
-/
scoped infixr:90 "₊ " => lanLift

@[simp]
/-
**CategoryTheory.Bicategory.lanLiftLeftLift_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：lanLiftLeftLift_lift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLi
ftLeftLift f g).lift = f₊ g
参数：f : b ⟶ a；g : c ⟶ a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lanLiftLeftLift_lift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (lanLiftLeftLift f g).lift = f₊ g := rfl

/-- The unit for the left Kan lift `f₊ g`. -/
/-
**CategoryTheory.Bicategory.lanLiftUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Bicategory`。
形式化陈述：lanLiftUnit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : g ⟶ f₊ g ≫ f
参数：f : b ⟶ a；g : c ⟶ a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit for the left Kan lift `f₊ g`.
-/
def lanLiftUnit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : g ⟶ f₊ g ≫ f :=
  (lanLiftLeftLift f g).unit

@[simp]
/-
**CategoryTheory.Bicategory.lanLiftLeftLift_unit** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory`。
形式化陈述：lanLiftLeftLift_unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLi
ftLeftLift f g).unit = lanLiftUnit f g
参数：f : b ⟶ a；g : c ⟶ a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lanLiftLeftLift_unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (lanLiftLeftLift f g).unit = lanLiftUnit f g := rfl

/-- Evidence that `lanLiftLeftLift f g` is a Kan lift. -/
/-
**CategoryTheory.Bicategory.lanLiftIsKan** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Bicategory`。
形式化陈述：lanLiftIsKan (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLiftLeftLi
ft f g).IsKan
参数：f : b ⟶ a；g : c ⟶ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.instHasInitialLeftLiftOfHasLeftKanLift`：∀ {B :
 Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : b ⟶ a} {g : c ⟶ a
}   [CategoryTheory.Bicategory.HasLeftKanLift f g],   …

--- 原说明 ---
Evidence that `lanLiftLeftLift f g` is a Kan lift.
-/
def lanLiftIsKan (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLiftLeftLift f g).IsKan :=
  initialIsInitial

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The family of 2-morphisms out of the left Kan lift `f₊ g`. -/
/-
**CategoryTheory.Bicategory.lanLiftDesc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Bicategory`。
形式化陈述：lanLiftDesc [HasLeftKanLift f g] (s : LeftLift f g) : f₊ g ⟶ s.lift
参数：s : LeftLift f g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of 2-morphisms out of the left Kan lift `f₊ g`.
-/
def lanLiftDesc [HasLeftKanLift f g] (s : LeftLift f g) :
    f₊ g ⟶ s.lift :=
  (lanLiftIsKan f g).desc s

@[reassoc (attr := simp)]
/-
**CategoryTheory.Bicategory.lanLiftUnit_desc** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Bicategory`。
形式化陈述：lanLiftUnit_desc [HasLeftKanLift f g] (s : LeftLift f g) : lanLiftUnit f g
 ≫ lanLiftDesc s ▷ f = s.unit
参数：s : LeftLift f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LeftLift.IsKan.fac`：fac (H : IsKan t) (s : Lef
tLift f g) : t.unit ≫ H.desc s ▷ f = s.unit
-/
theorem lanLiftUnit_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    lanLiftUnit f g ≫ lanLiftDesc s ▷ f = s.unit :=
  (lanLiftIsKan f g).fac s

@[simp]
/-
**CategoryTheory.Bicategory.lanLiftIsKan_desc** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Bicategory`。
形式化陈述：lanLiftIsKan_desc [HasLeftKanLift f g] (s : LeftLift f g) : (lanLiftIsKan 
f g).desc s = lanLiftDesc s
参数：s : LeftLift f g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lanLiftIsKan_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    (lanLiftIsKan f g).desc s = lanLiftDesc s :=
  rfl
/-
**CategoryTheory.Bicategory.LanLift.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Bicategory.LanLift`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : b ⟶ a
} {g : c ⟶ a}   [inst_1 : CategoryTheory.Bicategory.HasLeftKanLift f g] (s : Cat
egoryTheory.Bicategory.LeftLift f g),   ∃! τ,     CategoryTheory.CategoryStruct.
comp (CategoryTheory.Bicategory.lanLiftUnit f g)         (CategoryTheory.Bicateg
ory.whiskerRight τ f) =       s.unit
参数：s : CategoryTheory.Bicategory.LeftLift f g；CategoryTheory.Bicategory.lanLiftU
nit f g；CategoryTheory.Bicategory.whiskerRight τ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.IsUniversal.existsUnique`：existsUnique (h
 : IsUniversal f) (g : StructuredArrow S T) : exists! η : f.right ⟶ g.right, f.h
om ≫ T.map η = g.hom
-/
theorem LanLift.existsUnique [HasLeftKanLift f g] (s : LeftLift f g) :
    ∃! τ, lanLiftUnit f g ≫ τ ▷ f = s.unit :=
  (lanLiftIsKan f g).existsUnique _

/-- We say that a 1-morphism `h` commutes with the left Kan lift `f₊ g` if the whiskered left lift
for `f₊ g` by `h` is a Kan lift of `h ≫ g` along `f`. -/
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Bicategory.LanLift`。
形式化陈述：{B : Type u} →   [inst : CategoryTheory.Bicategory B] →     {a b c : B} → 
(f : b ⟶ a) → (g : c ⟶ a) → [CategoryTheory.Bicategory.HasLeftKanLift f g] → {x 
: B} → (x ⟶ c) → Prop
参数：f : b ⟶ a；g : c ⟶ a；x ⟶ c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a 1-morphism `h` commutes with the left Kan lift `f₊ g` if the whisk
ered left lift
for `f₊ g` by `h` is a Kan lift of `h ≫ g` along `f`.
-/
class LanLift.CommuteWith
    (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] {x : B} (h : x ⟶ c) : Prop where
  commute : Nonempty <| IsKan <| (lanLiftLeftLift f g).whisker h

namespace LanLift.CommuteWith

/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.of_isKan_whisker** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：of_isKan_whisker [HasLeftKanLift f g] (t : LeftLift f g) {x : B} (h : x ⟶ 
c) (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLiftLeftLift f g).whisker h)
 : LanLift.CommuteWith f g h
参数：t : LeftLift f g；h : x ⟶ c；H : IsKan (t.whisker h)；i : t.whisker h ≅ (lanLift
LeftLift f g).whisker h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_isKan_whisker [HasLeftKanLift f g] (t : LeftLift f g) {x : B} (h : x ⟶ c)
    (H : IsKan (t.whisker h)) (i : t.whisker h ≅ (lanLiftLeftLift f g).whisker h) :
    LanLift.CommuteWith f g h :=
  ⟨⟨IsKan.ofIsoKan H i⟩⟩
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.of_lanLift_comp_iso** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：of_lanLift_comp_iso [HasLeftKanLift f g] {x : B} {h : x ⟶ c} [HasLeftKanLi
ft f (h ≫ g)] (i : f₊ (h ≫ g) ≅ h ≫ f₊ g) (w : lanLiftUnit f (h ≫ g) ≫ i.hom ▷ f
 = h ◁ lanLiftUnit f g ≫ (α_ _ _ _).inv) : LanLift.CommuteWith f g h
参数：h ≫ g；i : f₊ (h ≫ g) ≅ h ≫ f₊ g；w : lanLiftUnit f (h ≫ g) ≫ i.hom ▷ f = h ◁ l
anLiftUnit f g ≫ (α_ _ _ _).inv。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Bicategory.postcomp_map`：∀ {B : Type u} [inst : CategoryT
heory.Bicategory B] {b c : B} (a : B) (f : b ⟶ c) {X Y : a ⟶ b} (x : X ⟶ Y),   (
CategoryTheory.Bicategory.po…
-/
theorem of_lanLift_comp_iso [HasLeftKanLift f g]
    {x : B} {h : x ⟶ c} [HasLeftKanLift f (h ≫ g)]
    (i : f₊ (h ≫ g) ≅ h ≫ f₊ g)
    (w : lanLiftUnit f (h ≫ g) ≫ i.hom ▷ f = h ◁ lanLiftUnit f g ≫ (α_ _ _ _).inv) :
    LanLift.CommuteWith f g h :=
  ⟨⟨(lanLiftIsKan f (h ≫ g)).ofIsoKan <| StructuredArrow.isoMk i⟩⟩

variable (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
variable {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h]

/-- Evidence that `h` commutes with the left Kan lift `f₊ g`. -/
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.isKan** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：isKan : IsKan (lanLiftLeftLift f g).whisker h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LanLift.CommuteWith.commute`：∀ {B : Type u} {i
nst : CategoryTheory.Bicategory B} {a b c : B} {f : b ⟶ a} {g : c ⟶ a}   {inst_1
 : CategoryTheory.Bicategory.HasLeftKanLift…

--- 原说明 ---
Evidence that `h` commutes with the left Kan lift `f₊ g`.
-/
def isKan : IsKan <| (lanLiftLeftLift f g).whisker h :=
    Classical.choice LanLift.CommuteWith.commute
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Bicategory.LanLift.CommuteWith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLeftKanLift f (h ≫ g) := (LanLift.CommuteWith.isKan f g h).hasLeftKanLift

/-- If `h` commutes with `f₊ g` and `t` is another left Kan lift of `g` along `f`, then
`t.whisker h` is a left Kan lift of `h ≫ g` along `f`. -/
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.isKanWhisker** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：isKanWhisker (t : LeftLift f g) (H : IsKan t) {x : B} (h : x ⟶ c) [LanLift
.CommuteWith f g h] : IsKan (t.whisker h)
参数：t : LeftLift f g；H : IsKan t；h : x ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `h` commutes with `f₊ g` and `t` is another left Kan lift of `g` along `f`, t
hen
`t.whisker h` is a left Kan lift of `h ≫ g` along `f`.
-/
def isKanWhisker
    (t : LeftLift f g) (H : IsKan t) {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h] :
    IsKan (t.whisker h) :=
  IsKan.whiskerOfCommute (lanLiftLeftLift f g) t (IsKan.uniqueUpToIso (lanLiftIsKan f g) H) h
    (isKan f g h)

/-- The isomorphism `f₊ (h ≫ g) ≅ h ≫ f₊ g` at the level of structured arrows. -/
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.lanLiftCompIsoWhisker** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：lanLiftCompIsoWhisker : lanLiftLeftLift f (h ≫ g) ≅ (lanLiftLeftLift f g).
whisker h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LanLift.CommuteWith.instHasLeftKanLiftComp`：∀ 
{B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : b ⟶ a) (g : c
 ⟶ a)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanLift…

--- 原说明 ---
The isomorphism `f₊ (h ≫ g) ≅ h ≫ f₊ g` at the level of structured arrows.
-/
def lanLiftCompIsoWhisker :
    lanLiftLeftLift f (h ≫ g) ≅ (lanLiftLeftLift f g).whisker h :=
  IsKan.uniqueUpToIso (lanLiftIsKan f (h ≫ g)) (LanLift.CommuteWith.isKan f g h)

@[simp]
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.lanLiftCompIsoWhisker_hom_right*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：lanLiftCompIsoWhisker_hom_right : (lanLiftCompIsoWhisker f g h).hom.right 
= lanLiftDesc ((lanLiftLeftLift f g).whisker h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LanLift.CommuteWith.instHasLeftKanLiftComp`：∀ 
{B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : b ⟶ a) (g : c
 ⟶ a)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanLift…
-/
theorem lanLiftCompIsoWhisker_hom_right :
    (lanLiftCompIsoWhisker f g h).hom.right = lanLiftDesc ((lanLiftLeftLift f g).whisker h) :=
  rfl

@[simp]
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.lanLiftCompIsoWhisker_inv_right*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：lanLiftCompIsoWhisker_inv_right : (lanLiftCompIsoWhisker f g h).inv.right 
= (isKan f g h).desc (lanLiftLeftLift f (h ≫ g))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LanLift.CommuteWith.instHasLeftKanLiftComp`：∀ 
{B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : b ⟶ a) (g : c
 ⟶ a)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanLift…
-/
theorem lanLiftCompIsoWhisker_inv_right :
    (lanLiftCompIsoWhisker f g h).inv.right = (isKan f g h).desc (lanLiftLeftLift f (h ≫ g)) :=
  rfl

/-- The 1-morphism `h` commutes with the left Kan lift `f₊ g`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.LanLift.CommuteWith.lanLiftCompIso** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Bicategory.LanLift.CommuteWith`。
形式化陈述：lanLiftCompIso : f₊ (h ≫ g) ≅ h ≫ f₊ g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LanLift.CommuteWith.instHasLeftKanLiftComp`：∀ 
{B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} (f : b ⟶ a) (g : c
 ⟶ a)   [inst_1 : CategoryTheory.Bicategory.HasLeftKanLift…

--- 原说明 ---
The 1-morphism `h` commutes with the left Kan lift `f₊ g`.
-/
def lanLiftCompIso : f₊ (h ≫ g) ≅ h ≫ f₊ g := Comma.rightIso <| lanLiftCompIsoWhisker f g h

end LanLift.CommuteWith

/-- We say that there exists an absolute left Kan lift of `g` along `f` if any 1-morphism `h`
commutes with the left Kan lift `f₊ g`. -/
/-
**CategoryTheory.Bicategory.HasAbsLeftKanLift** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Bicategory`。
形式化陈述：{B : Type u} → [inst : CategoryTheory.Bicategory B] → {a b c : B} → (b ⟶ a
) → (c ⟶ a) → Prop
参数：b ⟶ a；c ⟶ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that there exists an absolute left Kan lift of `g` along `f` if any 1-mor
phism `h`
commutes with the left Kan lift `f₊ g`.
-/
class HasAbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop extends HasLeftKanLift f g where
  commute : ∀ {x : B} (h : x ⟶ c), LanLift.CommuteWith f g h
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasAbsLeftKanLift f g] {x : B} (h : x ⟶ c) : LanLift.CommuteWith f g h :=
  HasAbsLeftKanLift.commute h
/-
**CategoryTheory.Bicategory.LeftLift.IsAbsKan.hasAbsLeftKanLift** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Bicategory.LeftLift.IsAbsKan`。
形式化陈述：∀ {B : Type u} [inst : CategoryTheory.Bicategory B] {a b c : B} {f : b ⟶ a
} {g : c ⟶ a}   {t : CategoryTheory.Bicategory.LeftLift f g} (H : t.IsAbsKan), C
ategoryTheory.Bicategory.HasAbsLeftKanLift f g
参数：H : t.IsAbsKan。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Bicategory.LeftLift.IsKan.hasLeftKanLift`：∀ {B : Type u} 
[inst : CategoryTheory.Bicategory B] {a b c : B} {f : b ⟶ a} {g : c ⟶ a}   {t : 
CategoryTheory.Bicategory.LeftLift f g} (H : …
-/
theorem LeftLift.IsAbsKan.hasAbsLeftKanLift {t : LeftLift f g} (H : IsAbsKan t) :
    HasAbsLeftKanLift f g :=
  have : HasLeftKanLift f g := H.isKan.hasLeftKanLift
  ⟨fun h ↦ ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (lanLiftIsKan f g)) h⟩⟩⟩

end LeftLift

end Bicategory

end CategoryTheory

